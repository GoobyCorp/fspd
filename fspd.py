#!/usr/bin/env python3

__author__ = "GoobyCorp"
__description__ = "A script used to host a FSP server primarily for Swiss on the GameCube"
__credits__ = ["GoobyCorp", "Extrems"]

import re
import os
import argparse
import os.path as osp
from io import BytesIO
from enum import IntEnum
from random import randint
from struct import pack, unpack, pack_into, unpack_from, calcsize
from socketserver import ThreadingUDPServer, DatagramRequestHandler

FSP_HSIZE = 12
FSP_SPACE = 1024
FSP_MAX_SIZE = FSP_HSIZE + FSP_SPACE

KEY = None
FSP_UPLOAD_CACHE = "tmp.bin"

FSP_SERVER_DIR = "server"
FSP_PASSWORD = ""

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
	data = bytearray(data)
	pack_into("!B", data, FSPOffset.OFFS_CKSM, len(data) & 0xFF)
	cksm = -(len(data) & 0xFF)
	cksm += sum(data)
	cksm += cksm >> 8
	return cksm & 0xFF

class FSPOffset(IntEnum):
	OFFS_CMD  = 0
	OFFS_CKSM = 1

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

class FSPRDIRENTType(IntEnum):
	RDTYPE_END  = 0x00
	RDTYPE_FILE = 0x01
	RDTYPE_DIR  = 0x02
	RDTYPE_SKIP = 0x2A

class FSPRDIRENT:
	FSP_RDIRENT_FMT = "!2IB"

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
		dir_ent = FSPRDIRENT()
		if osp.isfile(path):
			dir_ent.time = 1592534256  # osp.getmtime(path)
			dir_ent.size = osp.getsize(path)
			dir_ent.type = FSPRDIRENTType.RDTYPE_FILE
			dir_ent.name = osp.basename(path)
		elif osp.isdir(path):
			dir_ent.time = 1592534256  # osp.getmtime(path)
			dir_ent.size = 0
			dir_ent.type = FSPRDIRENTType.RDTYPE_DIR
			dir_ent.name = osp.basename(path)

		return dir_ent

	@staticmethod
	def create_end():
		dir_ent = FSPRDIRENT()
		dir_ent.type = FSPRDIRENTType.RDTYPE_END

		return dir_ent

	def __bytes__(self) -> bytes:
		b = pack(self.FSP_RDIRENT_FMT, self.time, self.size, self.type)
		b += self.name.encode("UTF8")
		b += b"\x00" * calc_pad_size(b, 4)
		assert len(b) % 4 == 0, "Invalid RDIRENT size"
		return b

	def to_bytes(self) -> bytes:
		return bytes(self)

class FSPSTAT:
	FSP_STAT_FMT = "!2IB"

	time = 0
	size = 0
	type = 0

	def __init__(self):
		self.reset()

	def reset(self) -> None:
		self.time = 0
		self.size = 0
		self.type = 0
		self.name = ""

	@staticmethod
	def create(path: str):
		dir_ent = FSPRDIRENT()
		if osp.isfile(path):
			dir_ent.time = 1592534256  # osp.getmtime(path)
			dir_ent.size = osp.getsize(path)
			dir_ent.type = FSPRDIRENTType.RDTYPE_FILE
			dir_ent.name = osp.basename(path)
		elif osp.isdir(path):
			dir_ent.time = 1592534256  # osp.getmtime(path)
			dir_ent.size = 0
			dir_ent.type = FSPRDIRENTType.RDTYPE_DIR
			dir_ent.name = osp.basename(path)
		else:
			dir_ent.time = 0
			dir_ent.size = 0
			dir_ent.type = 0

		return dir_ent

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
		req = FSPRequest()
		(cmd, req.checksum, req.key, req.sequence, req.data_len, req.position) = unpack_from(FSPRequest.FSP_HDR_FMT, data, 0)
		req.command = FSPCommand(cmd)
		req.data = data[req.FSP_HDR_LEN:req.FSP_HDR_LEN + req.data_len]
		req.extra = data[req.FSP_HDR_LEN + req.data_len:]

		# verify the checksum
		calc_cksm = calc_cksm_client_to_server(req.to_bytes())
		assert req.checksum == calc_cksm, f"Invalid FSP checksum, received: 0x{req.checksum:02X}, calculated: 0x{calc_cksm:02X}"

		# command-specific parsing
		if req.command == FSPCommand.CC_GET_DIR:
			(req.directory, req.password) = [x.rstrip(b"\x00").decode("UTF8") for x in req.data.split(b"\n", 1)]
			req.directory = req.directory.lstrip("/")
			req.directory = "./" + FSP_SERVER_DIR + "/" + req.directory
		if req.command in [FSPCommand.CC_GET_FILE, FSPCommand.CC_STAT, FSPCommand.CC_DEL_FILE, FSPCommand.CC_INSTALL]:
			(req.filename, req.password) = [x.rstrip(b"\x00").decode("UTF8") for x in req.data.split(b"\n", 1)]
			req.filename = req.filename.lstrip("/")
			req.filename = "./" + FSP_SERVER_DIR + "/" + req.filename
			if req.command == FSPCommand.CC_GET_FILE and len(req.extra) == 2:
				(req.block_size,) = unpack("!H", req.extra)

		return req

	@staticmethod
	def create(cmd: (int, FSPCommand), data: (bytes, bytearray) = b"", pos: int = 0, seq: int = 0):
		global KEY

		fsp_req = FSPRequest()
		fsp_req.command = int(cmd)
		fsp_req.key = randint(0, 0xFFFF) if KEY is None else KEY
		fsp_req.sequence = seq
		fsp_req.data_len = len(data)
		fsp_req.position = pos
		fsp_req.data = data
		fsp_req.checksum = calc_cksm_server_to_client(fsp_req.to_bytes())

		if KEY is None:
			KEY = fsp_req.key

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
		self.fsp_req = FSPRequest.parse(self.rfile.read(FSP_MAX_SIZE))

		if self.fsp_req.command in [FSPCommand.CC_GET_DIR, FSPCommand.CC_GET_FILE, FSPCommand.CC_STAT, FSPCommand.CC_DEL_FILE, FSPCommand.CC_INSTALL]:
			if len(FSP_PASSWORD) > 0 and self.fsp_req.password != FSP_PASSWORD:
				print("Invalid password!")

				rep = FSPRequest.create(FSPCommand.CC_ERR, b"Invalid password!", 0, self.fsp_req.sequence).to_bytes()
				self.wfile.write(rep)
				return

		if self.fsp_req.command == FSPCommand.CC_GET_DIR:
			self.handle_get_dir()
		elif self.fsp_req.command == FSPCommand.CC_GET_FILE:
			self.handle_get_file()
		elif self.fsp_req.command == FSPCommand.CC_STAT:
			rep = FSPSTAT.create(self.fsp_req.filename).to_bytes()
			rep = FSPRequest.create(self.fsp_req.command, rep, self.fsp_req.position, self.fsp_req.sequence).to_bytes()
			self.wfile.write(rep)
		elif self.fsp_req.command == FSPCommand.CC_DEL_FILE:
			if osp.isfile(self.fsp_req.filename):
				os.remove(self.fsp_req.filename)
				rep = FSPRequest.create(self.fsp_req.command, b"", self.fsp_req.position, self.fsp_req.sequence).to_bytes()
				self.wfile.write(rep)
			else:
				rep = FSPRequest.create(FSPCommand.CC_ERR, b"Error deleting file!", 0, self.fsp_req.sequence).to_bytes()
				self.wfile.write(rep)
		elif self.fsp_req.command == FSPCommand.CC_UP_LOAD:
			self.handle_up_load()
		elif self.fsp_req.command == FSPCommand.CC_INSTALL:
			self.handle_install()
		elif self.fsp_req.command == FSPCommand.CC_BYE:
			rep = FSPRequest.create(self.fsp_req.command, b"", 0, self.fsp_req.sequence).to_bytes()
			self.wfile.write(rep)
		else:
			print(self.fsp_req.command)
			print("Key:", self.fsp_req.key)
			print("Seq:", self.fsp_req.sequence)
			print("Pos:", self.fsp_req.position)

			if len(self.fsp_req.data) > 0:
				print(self.fsp_req.data)

			if len(self.fsp_req.extra) > 0:
				print(self.fsp_req.extra)

	def handle_get_dir(self) -> None:
		size = 0
		files = os.listdir(self.fsp_req.directory)
		if len(files) > 0:
			dir_ents = b""
			for x in files:
				dir_ents += FSPRDIRENT.create(osp.join(self.fsp_req.directory, x)).to_bytes()
			size = len(dir_ents)
			rep = FSPRequest.create(self.fsp_req.command, dir_ents, 0, self.fsp_req.sequence).to_bytes()
			self.socket.sendto(rep, self.client_address)

		rep = FSPRequest.create(self.fsp_req.command, FSPRDIRENT.create_end().to_bytes(), size, self.fsp_req.sequence).to_bytes()
		self.socket.sendto(rep, self.client_address)

	def handle_get_file(self) -> None:
		global FSP_GET_FILE_CACHE
		global FSP_GET_FILE_CACHE_FILENAME

		self.fsp_req.block_size = FSP_SPACE

		with open(self.fsp_req.filename, "rb") as f:
			f.seek(self.fsp_req.position)
			buf = f.read(self.fsp_req.block_size)

		rep = FSPRequest.create(self.fsp_req.command, buf, self.fsp_req.position, self.fsp_req.sequence).to_bytes()
		with BytesIO(rep) as bio:
			while (buf := bio.read(65507)) != b"":
				self.wfile.write(buf)

	def handle_up_load(self) -> None:
		global FSP_UPLOAD_CACHE

		with open(FSP_UPLOAD_CACHE, "a+b") as f:
			f.seek(self.fsp_req.position)
			f.write(self.fsp_req.data)

		rep = FSPRequest.create(self.fsp_req.command, b"", self.fsp_req.position, self.fsp_req.sequence).to_bytes()
		self.wfile.write(rep)

	def handle_install(self) -> None:
		global FSP_UPLOAD_CACHE

		os.rename(FSP_UPLOAD_CACHE, self.fsp_req.filename)

		rep = FSPRequest.create(self.fsp_req.command, b"", 0, self.fsp_req.sequence).to_bytes()
		self.wfile.write(rep)

# https://sourceforge.net/p/fsp/code/ci/master/tree/doc/PROTOCOL
# https://github.com/emukidid/swiss-gc/blob/master/cube/swiss/source/devices/fsp/deviceHandler-FSP.c
# https://github.com/emukidid/swiss-gc/blob/master/cube/swiss/source/devices/fsp/fsplib.c

def parse_hostname_port(s: str):
	hostname_port_exp = re.compile(r"\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}:\d{1,5}")
	if hostname_port_exp.fullmatch(s):
		(hostname, port) = s.split(":", 1)
		return (hostname, int(port))

def main() -> None:
	global FSP_PASSWORD

	parser = argparse.ArgumentParser(description=__description__)
	parser.add_argument("-a", "--address", type=parse_hostname_port, default=("0.0.0.0", 7717), help="The address to bind to")
	parser.add_argument("-p", "--password", default="", type=str, help="The password to use")
	args = parser.parse_args()

	assert type(args.address) == tuple, "Invalid address:port pair specified"

	FSP_PASSWORD = args.password

	if not osp.isdir(FSP_SERVER_DIR):
		print("Creating server directory...")
		os.mkdir(FSP_SERVER_DIR)

	print(f"FSP server running on {args.address[0]}:{args.address[1]}...")
	with ThreadingUDPServer((args.address[0], args.address[1]), FSPRequestHandler) as server:
		server.serve_forever()

if __name__ == "__main__":
	main()