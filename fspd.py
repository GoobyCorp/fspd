#!/usr/bin/env python3

__author__ = "GoobyCorp"
__description__ = "A script used to host an FSP server primarily for Swiss on the Nintendo GameCube or Wii(U)"
__credits__ = ["GoobyCorp", "Extrems"]
__references__ = [
	"https://sourceforge.net/p/fsp/code/ci/master/tree/doc/PROTOCOL",
	"https://github.com/emukidid/swiss-gc/blob/master/cube/swiss/source/devices/fsp/deviceHandler-FSP.c",
	"https://github.com/emukidid/swiss-gc/blob/master/cube/swiss/source/devices/fsp/fsplib.c"
]

import re
import os
import zlib
import socket
import argparse
import os.path as osp
from io import BytesIO
from enum import IntEnum
from random import randint
from sys import version_info
from struct import pack, unpack, pack_into, unpack_from, calcsize
from socketserver import ThreadingUDPServer, DatagramRequestHandler

from math import floor, ceil

# constants
FSP_HSIZE = 12
FSP_SPACE = 1024
FSP_MAXSPACE = FSP_HSIZE + FSP_SPACE
FSP_UP_LOAD_CACHE_FILE = "tmp.bin"

# global variables
FSP_KEY = None
FSP_SERVER_DIR = ""
FSP_PASSWORD = ""
# caches
FSP_LAST_GET_DIR = ""
FSP_LAST_GET_DIR_CACHE = b""
FSP_LAST_GET_FILE = ""
FSP_LAST_GCZ_FILE = None

def calc_pad_size(data: (bytes, bytearray), boundary: int) -> int:
	return boundary - len(data) % boundary

def calc_cksm_client_to_server(data: (bytes, bytearray)) -> int:
	if type(data) == bytes:
		data = bytearray(data)
	pack_into("!B", data, FSPOffset.OFFS_CKSM, 0)
	cksm = 0
	cksm += sum(data)
	cksm += len(data)
	cksm += cksm >> 8
	return cksm & 0xFF

def calc_cksm_server_to_client(data: (bytes, bytearray)) -> int:
	if type(data) == bytes:
		data = bytearray(data)
	pack_into("!B", data, FSPOffset.OFFS_CKSM, len(data) & 0xFF)
	cksm = -(len(data) & 0xFF)
	cksm += sum(data)
	cksm += cksm >> 8
	return cksm & 0xFF

class FSPOffset(IntEnum):
	OFFS_CMD      = 0  # 0-1
	OFFS_CKSM     = 1  # 1-2
	OFFS_KEY      = 2  # 2-4
	OFFS_SEQ      = 4  # 4-6
	OFFS_DATA_LEN = 6  # 6-8
	OFFS_POS      = 8  # 8-12

class FSPCommand(IntEnum):
	CC_VERSION   = 0x10
	CC_ERR       = 0x40
	CC_GET_DIR   = 0x41
	CC_GET_FILE  = 0x42
	CC_UP_LOAD   = 0x43
	CC_INSTALL   = 0x44
	CC_DEL_FILE  = 0x45
	CC_DEL_DIR   = 0x46
	CC_GET_PRO   = 0x47
	CC_SET_PRO   = 0x48
	CC_MAKE_DIR  = 0x49
	CC_BYE       = 0x4A
	CC_GRAB_FILE = 0x4B
	CC_GRAB_DONE = 0x4C
	CC_STAT      = 0x4D
	CC_RENAME    = 0x4E
	CC_CH_PASSW  = 0x4F
	CC_LIMIT     = 0x80
	CC_TEST      = 0x81

class RDIRENTType(IntEnum):
	RDTYPE_END  = 0x00
	RDTYPE_FILE = 0x01
	RDTYPE_DIR  = 0x02
	RDTYPE_SKIP = 0x2A

class GCZImageType(IntEnum):
	GameCube = 0
	Wii = 1

class GCZImage:
	GCZ_MAGIC = 0xB10BC001
	GCZ_FMT = "<2I 2Q 2I"

	# header
	sub_type = None
	compressed_data_size = None
	data_size = None
	block_size = None
	num_blocks = None

	offsets = ()
	hashes = ()

	# helpers
	data_offset = None
	filename = None

	# stream variables
	stream = None
	offset = 0
	block_num = 0
	block_offset = 0

	def __init__(self, path: str):
		self.reset()
		assert osp.isfile(path), "GCZ file doesn't exist"
		self.filename = path
		self.stream = open(path, "rb")
		(magic, sub_type, self.compressed_data_size, self.data_size, self.block_size, self.num_blocks) = unpack(self.GCZ_FMT, self.stream.read(32))
		self.sub_type = GCZImageType(sub_type)
		assert magic == self.GCZ_MAGIC, "Invalid GCZ magic"
		assert self.block_size * self.num_blocks == self.data_size, "Invalid GCZ image size"
		self.offsets = unpack(f"<{self.num_blocks}Q", self.stream.read(self.num_blocks * calcsize("Q")))
		self.hashes = unpack(f"<{self.num_blocks}I", self.stream.read(self.num_blocks * calcsize("I")))
		self.data_offset = self.stream.tell()

	def __enter__(self):
		return self

	def __exit__(self, exc_type, exc_val, exc_tb) -> None:
		self.close()

	def reset(self) -> None:
		self.sub_type = None
		self.compressed_data_size = None
		self.data_size = None
		self.block_size = None
		self.num_blocks = None

		self.offsets = ()
		self.hashes = ()

		self.data_offset = None
		self.filename = None

		self.stream = None
		self.offset = 0
		self.block_num = 0
		self.block_offset = 0

	def is_block_compressed(self, num: int) -> bool:
		return self.offsets[num] >> 56 != 0x80

	def get_decompressed_block_offset(self, num: int) -> int:
		return num * self.block_size

	def get_compressed_block_offset(self, num: int) -> int:
		if not self.is_block_compressed(num):  # not compressed
			return self.data_offset + (self.offsets[num] & 0xFFFFFFFFFFFFFF)
		return self.data_offset + self.offsets[num]

	def get_compressed_block_size(self, num: int) -> int:
		blk_start = self.get_compressed_block_offset(num)
		if num < self.num_blocks - 1:
			return self.get_compressed_block_offset(num + 1) - blk_start
		elif num == self.num_blocks - 1:
			return abs(self.compressed_data_size - blk_start)
		else:
			raise IOError(f"Illegal block number {num}")

	def read_block(self, num: int) -> bytes:
		# no idea why this is needed?
		if num > self.num_blocks - 1:
			num = self.num_blocks - 1

		blk_start = self.get_compressed_block_offset(num)
		blk_size = self.get_compressed_block_size(num)

		self.stream.seek(blk_start)
		blk_data = self.stream.read(blk_size)
		blk_hash = zlib.adler32(blk_data) & 0xFFFFFFFF
		assert blk_hash == self.hashes[num], f"Invalid block hash for block {num}, computed: {blk_hash:04x}, got: {self.hashes[num]:04x}"

		if self.is_block_compressed(num):
			blk_data = zlib.decompress(blk_data, zlib.MAX_WBITS, self.block_size + 64)

		assert len(blk_data) == self.block_size, f"Invalid decompressed data size for block {num}, expected: {self.block_size}, got: {len(blk_data)}"

		return blk_data

	def size(self) -> int:
		return self.data_size

	def tell(self) -> int:
		return self.offset

	def seek(self, offset: int) -> bool:
		self.block_num = offset // self.block_size
		self.block_offset = offset - (self.block_num * self.block_size)
		self.offset = offset
		return self.offset <= self.data_size

	def read(self, size: int) -> bytes:
		# this should handle overlapping and non-overlapping reads
		left = size
		with BytesIO() as bio:
			while left != 0:
				tmp = self.read_block(self.block_num)
				# start at block offset for first block
				if left == size:
					tmp = tmp[self.block_offset:]
				# truncate last block if needed
				if left <= len(tmp):
					tmp = tmp[:left]
					self.block_offset = len(tmp)
				left -= len(tmp)
				# increment the block number if not the last block
				if left > 0:
					self.block_num += 1
				bio.write(tmp)
			data = bio.getvalue()
		self.offset += size
		return data

	def copy(self, stream) -> None:
		for i in range(self.num_blocks):
			stream.write(self.read_block(i))

	def close(self) -> None:
		if self.stream is not None:
			self.stream.close()

class RDIRENT:
	RDIRENT_FMT = "!2IB"
	RDIRENT_LEN = calcsize(RDIRENT_FMT)

	time = 0
	size = 0
	type = 0
	name = ""

	def __init__(self):
		self.reset()

	def reset(self) -> None:
		self.time = 0
		self.size = 0
		self.type = 0
		self.name = ""

	@staticmethod
	def create(path: str):
		rdir_ent = RDIRENT()
		if osp.isfile(path):
			rdir_ent.time = 1592534256  # osp.getmtime(path)
			rdir_ent.size = osp.getsize(path)
			rdir_ent.type = RDIRENTType.RDTYPE_FILE
			rdir_ent.name = osp.basename(path)
		elif osp.isdir(path):
			rdir_ent.time = 1592534256  # osp.getmtime(path)
			rdir_ent.size = 0
			rdir_ent.type = RDIRENTType.RDTYPE_DIR
			rdir_ent.name = osp.basename(path)

		return rdir_ent

	@staticmethod
	def create_skip():
		rdir_ent = RDIRENT()
		rdir_ent.type = RDIRENTType.RDTYPE_SKIP

		return rdir_ent

	@staticmethod
	def create_end():
		rdir_ent = RDIRENT()
		rdir_ent.type = RDIRENTType.RDTYPE_END

		return rdir_ent

	def __bytes__(self) -> bytes:
		b = pack(self.RDIRENT_FMT, self.time, self.size, self.type)
		b += self.name.encode("UTF8")
		b += b"\x00" * calc_pad_size(b, 4)
		assert len(b) % 4 == 0, "Invalid RDIRENT size"
		return b

	def __len__(self) -> int:
		return len(self.to_bytes())

	def to_bytes(self) -> bytes:
		return bytes(self)

class FSPSTAT:
	FSP_STAT_FMT = "!2IB"
	FSP_STAT_LEN = calcsize(FSP_STAT_FMT)

	time = 0
	size = 0
	type = 0

	def __init__(self):
		self.reset()

	def reset(self) -> None:
		self.time = 0
		self.size = 0
		self.type = 0

	@staticmethod
	def create(path: str):
		stat = FSPSTAT()
		if osp.isfile(path):
			stat.time = 1592534256  # osp.getmtime(path)
			stat.size = osp.getsize(path)
			stat.type = RDIRENTType.RDTYPE_FILE
		elif osp.isdir(path):
			stat.time = 1592534256  # osp.getmtime(path)
			stat.size = 0
			stat.type = RDIRENTType.RDTYPE_DIR
		else:
			stat.time = 0
			stat.size = 0
			stat.type = 0

		return stat

	def __bytes__(self) -> bytes:
		return pack(self.FSP_STAT_FMT, self.time, self.size, self.type)

	def to_bytes(self) -> bytes:
		return bytes(self)

class FSPRequest:
	FSP_HDR_FMT = "!2B3HI"
	FSP_HDR_LEN = calcsize(FSP_HDR_FMT)

	command: (int, FSPCommand) = 0
	checksum = 0
	key = 0
	sequence = 0
	data_len = 0
	position = 0
	data = b""
	extra = b""

	# command-specific variables
	directory = ""
	password = ""
	filename = ""
	block_size = FSP_SPACE

	def __init__(self):
		self.reset()

	def reset(self) -> None:
		self.command = 0
		self.checksum = 0
		self.key = 0
		self.sequence = 0
		self.data_len = 0
		self.position = 0
		self.data = b""
		self.extra = b""

		self.directory = ""
		self.password = ""
		self.filename = ""

	@staticmethod
	def parse(data: (bytes, bytearray)):
		# parse header
		fsp_req = FSPRequest()
		(cmd, fsp_req.checksum, fsp_req.key, fsp_req.sequence, fsp_req.data_len, fsp_req.position) = unpack_from(FSPRequest.FSP_HDR_FMT, data, 0)
		fsp_req.command = FSPCommand(cmd)
		fsp_req.data = data[FSPRequest.FSP_HDR_LEN:FSPRequest.FSP_HDR_LEN + fsp_req.data_len]
		fsp_req.extra = data[FSPRequest.FSP_HDR_LEN + fsp_req.data_len:]

		# verify the checksum
		calc_cksm = calc_cksm_client_to_server(fsp_req.to_bytes())
		assert fsp_req.checksum == calc_cksm, f"Invalid FSP checksum, received: 0x{fsp_req.checksum:02X}, calculated: 0x{calc_cksm:02X}"

		# command-specific parsing
		if fsp_req.command == FSPCommand.CC_GET_DIR:
			(fsp_req.directory, fsp_req.password) = [x.rstrip(b"\x00").decode("UTF8") for x in fsp_req.data.split(b"\n", 1)]
			# fsp_req.directory = fsp_req.directory.lstrip("/")
			fsp_req.directory = osp.join(FSP_SERVER_DIR, fsp_req.directory.lstrip("/"))
		if fsp_req.command in [FSPCommand.CC_GET_FILE, FSPCommand.CC_STAT, FSPCommand.CC_DEL_FILE, FSPCommand.CC_INSTALL]:
			(fsp_req.filename, fsp_req.password) = [x.rstrip(b"\x00").decode("UTF8") for x in fsp_req.data.split(b"\n", 1)]
			# fsp_req.filename = fsp_req.filename.lstrip("/")
			fsp_req.filename = osp.join(FSP_SERVER_DIR, fsp_req.filename.lstrip("/"))
			if fsp_req.command in [FSPCommand.CC_GET_DIR, FSPCommand.CC_GET_FILE] and len(fsp_req.extra) == 2:
				(fsp_req.block_size,) = unpack("!H", fsp_req.extra)

		return fsp_req

	@staticmethod
	def create(cmd: (int, FSPCommand), data: (bytes, bytearray) = b"", pos: int = 0, seq: int = 0):
		global FSP_KEY

		fsp_req = FSPRequest()
		fsp_req.command = int(cmd)
		fsp_req.key = randint(0, 0xFFFF) if FSP_KEY is None else FSP_KEY
		fsp_req.sequence = seq
		fsp_req.data_len = len(data)
		fsp_req.position = pos
		fsp_req.data = data
		fsp_req.checksum = calc_cksm_server_to_client(fsp_req.to_bytes())

		if FSP_KEY is None:
			FSP_KEY = fsp_req.key

		return fsp_req

	def __len__(self) -> int:
		return calcsize(self.FSP_HDR_FMT) + len(self.data) + len(self.extra)

	def __bytes__(self) -> bytes:
		b = pack(self.FSP_HDR_FMT, self.command, self.checksum, self.key, self.sequence, self.data_len, self.position)
		b += self.data
		b += self.extra
		return b

	def size(self) -> int:
		return len(self)

	def to_bytes(self) -> bytes:
		return bytes(self)

class FSPRequestHandler(DatagramRequestHandler):
	fsp_req = None
	socket = None

	def handle(self) -> None:
		global FSP_LAST_GET_FILE

		data = self.rfile.read(FSP_MAXSPACE)

		# Handle Swiss broadcast message
		if data == b"Swiss Broadcast Message":
			print("Handling Swiss broadcast message...")
			self.wfile.write(data)
			return

		self.fsp_req = FSPRequest.parse(data)

		if self.fsp_req.command in [FSPCommand.CC_GET_DIR, FSPCommand.CC_GET_FILE, FSPCommand.CC_STAT, FSPCommand.CC_DEL_FILE, FSPCommand.CC_INSTALL]:
			if not self.check_password():
				return

		if self.fsp_req.command == FSPCommand.CC_GET_DIR:
			self.handle_get_dir()
		elif self.fsp_req.command == FSPCommand.CC_GET_FILE:
			self.handle_get_file()
		elif self.fsp_req.command == FSPCommand.CC_UP_LOAD:
			self.handle_up_load()
		elif self.fsp_req.command == FSPCommand.CC_INSTALL:
			self.handle_install()
		elif self.fsp_req.command == FSPCommand.CC_DEL_FILE:
			self.handle_del_file()
		elif self.fsp_req.command == FSPCommand.CC_BYE:
			self.handle_bye()
		elif self.fsp_req.command == FSPCommand.CC_STAT:
			self.handle_stat()
		else:
			self.handle_unhandled()

	def check_password(self) -> bool:
		if len(FSP_PASSWORD) > 0 and self.fsp_req.password != FSP_PASSWORD:
			print("Invalid password!")

			rep = FSPRequest.create(FSPCommand.CC_ERR, b"Invalid password!", 0, self.fsp_req.sequence).to_bytes()
			self.wfile.write(rep)
			return False
		return True

	def handle_get_dir(self) -> None:
		print(self.fsp_req.position)

		rdir_ents = []
		files = os.listdir(self.fsp_req.directory)
		if len(files) > 0:
			for x in files:
				# serve .gcz files as .iso files
				if x.endswith(".gcz"):
					rdir_ent = RDIRENT()
					rdir_ent.time = 1592534256
					rdir_ent.size = GCZImage(osp.join(self.fsp_req.directory, x)).data_size
					rdir_ent.type = RDIRENTType.RDTYPE_FILE
					rdir_ent.name = x.replace(".gcz", ".iso")
				else:  # serve a regular file
					rdir_ent = RDIRENT.create(osp.join(self.fsp_req.directory, x))
				rdir_ents.append(rdir_ent.to_bytes())

		rdir_ents.append(RDIRENT.create_end().to_bytes())

		rdir_pkts = []
		while True:
			rdir_pkt = b""
			while len(rdir_ents) > 0:
				# grab the first entry
				rdir_ent = rdir_ents.pop(0)
				# entry will overlap directory block boundary
				if len(rdir_pkt) + len(rdir_ent) > FSP_SPACE:
					# pad to boundary
					if len(rdir_pkt) + RDIRENT.RDIRENT_LEN > FSP_SPACE:
						rdir_pkt += b"\x00" * calc_pad_size(rdir_pkt, FSP_SPACE)
					else:  # send skip and pad to boundary
						rdir_pkt += RDIRENT.create_skip().to_bytes()
						rdir_pkt += b"\x00" * calc_pad_size(rdir_pkt, FSP_SPACE)
					# we couldn't add it to the current packet so add it back to the queue
					rdir_ents.insert(0, rdir_ent)
					# packet is full so leave the loop and append it to the send queue
					break
				elif len(rdir_pkt) + len(rdir_ent) <= FSP_SPACE:
					rdir_pkt += rdir_ent
			rdir_pkts.append(rdir_pkt)
			# no more entries left so let's leave the loop and send them
			if len(rdir_ents) == 0:
				break

		for pkt in rdir_pkts:
			rep = FSPRequest.create(self.fsp_req.command, pkt[self.fsp_req.position:], self.fsp_req.position, self.fsp_req.sequence).to_bytes()
			self.socket.sendto(rep, self.client_address)

	def handle_get_file(self) -> None:
		global FSP_LAST_GET_FILE, FSP_LAST_GCZ_FILE

		self.fsp_req.block_size = FSP_SPACE

		if (FSP_LAST_GET_FILE == "" or FSP_LAST_GET_FILE != self.fsp_req.filename):
			FSP_LAST_GET_FILE = self.fsp_req.filename
			print(f"Serving file \"{self.fsp_req.filename}\"...")

		# check if the file being served is a .gcz file
		if self.fsp_req.filename.endswith(".iso") and not osp.isfile(self.fsp_req.filename):
			gcz_filename = self.fsp_req.filename.replace(".iso", ".gcz")
			if osp.isfile(gcz_filename):
				if FSP_LAST_GCZ_FILE is None:
					gcz = GCZImage(gcz_filename)
					gcz.seek(self.fsp_req.position)
					buf = gcz.read(self.fsp_req.block_size)
					FSP_LAST_GCZ_FILE = gcz
				elif FSP_LAST_GCZ_FILE is not None and FSP_LAST_GCZ_FILE.filename != FSP_LAST_GET_FILE.replace(".iso", ".gcz"):
					FSP_LAST_GCZ_FILE.close()
					FSP_LAST_GCZ_FILE = None

					gcz = GCZImage(gcz_filename)
					gcz.seek(self.fsp_req.position)
					buf = gcz.read(self.fsp_req.block_size)
					FSP_LAST_GCZ_FILE = gcz
				else:
					# print(f"Reading GCZ from cache \"{gcz_filename}\"")
					FSP_LAST_GCZ_FILE.seek(self.fsp_req.position)
					buf = FSP_LAST_GCZ_FILE.read(self.fsp_req.block_size)
		else:  # serve a regular file
			if FSP_LAST_GCZ_FILE is not None:
				print("Clearing GCZ cache...")
				FSP_LAST_GCZ_FILE.close()
				FSP_LAST_GCZ_FILE = None

			with open(self.fsp_req.filename, "rb") as f:
				f.seek(self.fsp_req.position)
				buf = f.read(self.fsp_req.block_size)

		rep = FSPRequest.create(self.fsp_req.command, buf, self.fsp_req.position, self.fsp_req.sequence).to_bytes()
		with BytesIO(rep) as bio:
			while (buf := bio.read(65507)) != b"":
				self.wfile.write(buf)

	def handle_up_load(self) -> None:
		with open(FSP_UP_LOAD_CACHE_FILE, "a+b") as f:
			f.seek(self.fsp_req.position)
			f.write(self.fsp_req.data)

		rep = FSPRequest.create(self.fsp_req.command, b"", self.fsp_req.position, self.fsp_req.sequence).to_bytes()
		self.wfile.write(rep)

	def handle_install(self) -> None:
		print(f"Installing file to \"{self.fsp_req.filename}\"...")

		os.rename(FSP_UP_LOAD_CACHE_FILE, self.fsp_req.filename)

		rep = FSPRequest.create(self.fsp_req.command, b"", 0, self.fsp_req.sequence).to_bytes()
		self.wfile.write(rep)

	def handle_del_file(self) -> None:
		print(f"Deleting file \"{self.fsp_req.filename}\"...")

		if osp.isfile(self.fsp_req.filename):
			os.remove(self.fsp_req.filename)
			rep = FSPRequest.create(self.fsp_req.command, b"", self.fsp_req.position, self.fsp_req.sequence).to_bytes()
		else:
			rep = FSPRequest.create(FSPCommand.CC_ERR, b"Error deleting file!", 0, self.fsp_req.sequence).to_bytes()
		self.wfile.write(rep)

	def handle_bye(self) -> None:
		# print("Bye!")

		rep = FSPRequest.create(self.fsp_req.command, b"", 0, self.fsp_req.sequence).to_bytes()
		self.wfile.write(rep)

	def handle_stat(self) -> None:
		print(f"Stat'ing file \"{self.fsp_req.filename}\"...")

		# stat a .gcz file
		if self.fsp_req.filename.endswith(".iso") and not osp.isfile(self.fsp_req.filename):
			gcz_filename = self.fsp_req.filename.replace(".iso", ".gcz")
			if osp.isfile(gcz_filename):
				stat = FSPSTAT()
				stat.time = 1592534256
				stat.size = GCZImage(gcz_filename).data_size
				stat.type = RDIRENTType.RDTYPE_FILE
				rep = stat.to_bytes()
		else:  # stat a regular file
			rep = FSPSTAT.create(self.fsp_req.filename).to_bytes()
		rep = FSPRequest.create(self.fsp_req.command, rep, self.fsp_req.position, self.fsp_req.sequence).to_bytes()
		self.wfile.write(rep)

	def handle_unhandled(self) -> None:
		print(self.fsp_req.command)
		print("Key:", self.fsp_req.key)
		print("Seq:", self.fsp_req.sequence)
		print("Pos:", self.fsp_req.position)

		if len(self.fsp_req.data) > 0:
			print(self.fsp_req.data)

		if len(self.fsp_req.extra) > 0:
			print(self.fsp_req.extra)

def parse_hostname_port(s: str):
	hostname_port_exp = re.compile(r"\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}:\d{1,5}")
	if hostname_port_exp.fullmatch(s):
		(hostname, port) = s.split(":", 1)
		return (hostname, int(port))

def main() -> None:
	global FSP_PASSWORD, FSP_SERVER_DIR

	# check python version before running
	assert version_info.major == 3 and version_info.minor >= 8, "This script requires Python 3.8 or greater!"

	parser = argparse.ArgumentParser(description=__description__)
	parser.add_argument("-a", "--address", type=parse_hostname_port, default=("0.0.0.0", 7717), help="The address to bind to")
	parser.add_argument("-p", "--password", type=str, default="", help="The password to use")
	parser.add_argument("-d", "--directory", type=str, default="server", help="The directory to serve from")
	args = parser.parse_args()

	assert type(args.address) == tuple, "Invalid address:port pair specified"

	FSP_PASSWORD = args.password
	FSP_SERVER_DIR = args.directory

	assert osp.isdir(FSP_SERVER_DIR), "The specified server directory doesn't exist"

	print(f"FSP server running on {args.address[0]}:{args.address[1]}...")
	print(f"Base Directory: \"{osp.abspath(FSP_SERVER_DIR)}\"")
	with ThreadingUDPServer((args.address[0], args.address[1]), FSPRequestHandler) as server:
		server.socket.setsockopt(socket.SOL_SOCKET, socket.SO_BROADCAST, 1)
		server.socket.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
		server.serve_forever()

if __name__ == "__main__":
	main()