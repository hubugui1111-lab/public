#!/usr/bin/env python3
"""Patch ladnir/secure-join with the Exp187 fixed-weight secret-shuffle benchmark."""
from pathlib import Path

root = Path(__import__("sys").argv[1]).resolve()
cpp = root / "frontend" / "benchmark.cpp"
hdr = root / "frontend" / "benchmark.h"
main = root / "frontend" / "main.cpp"

s = cpp.read_text()
inc = '#include "secure-join/Perm/AltModComposedPerm.h"\n'
if inc not in s:
    s = s.replace('#include "secure-join/Perm/PprfPermGen.h"\n',
                  '#include "secure-join/Perm/PprfPermGen.h"\n' + inc)

marker = "\n\tvoid AltModPerm_benchmark(const oc::CLP& cmd)\n"
if "void Exp187_shuffle_benchmark" not in s:
    fn = r'''
	void Exp187_shuffle_benchmark(const oc::CLP& cmd)
	{
		u64 N = cmd.getOr("n", 3072ull);
		u64 B = cmd.getOr("B", 320ull);
		u64 w = cmd.getOr("w", 214ull);
		u64 nt = cmd.getOr("nt", 2ull);
		u64 batch = 1ull << cmd.getOr("b", 16);
		bool mock = cmd.getOr("mock", 0);
		if (w > B) throw RTE_LOC;
		const u64 M = N + B;
		const u64 fwdBytes = 7; // 1-byte flag + 48-bit payload
		const u64 invBytes = 6; // 48-bit payload only
		const u64 setupBytes = fwdBytes + invBytes;

		macoro::thread_pool pool0, pool1;
		auto e0 = pool0.make_work();
		auto e1 = pool1.make_work();
		pool0.create_threads(nt);
		pool1.create_threads(nt);

		auto genSock = coproto::LocalAsyncSocket::makePair();
		auto corSock = coproto::LocalAsyncSocket::makePair();
		auto onlineSock = coproto::LocalAsyncSocket::makePair();
		for (auto* p : {&genSock[0], &corSock[0], &onlineSock[0]}) p->setExecutor(pool0);
		for (auto* p : {&genSock[1], &corSock[1], &onlineSock[1]}) p->setExecutor(pool1);

		PRNG prng0(oc::ZeroBlock), prng1(oc::OneBlock);
		CorGenerator g0, g1;
		g0.init(corSock[0].fork(), prng0, 0, nt, batch, mock);
		g1.init(corSock[1].fork(), prng1, 1, nt, batch, mock);
		g0.mGenState->mPool = &pool0;
		g1.mGenState->mPool = &pool1;

		AltModComposedPerm pg0, pg1;
		pg0.init(0, M, setupBytes, g0);
		pg1.init(1, M, setupBytes, g1);
		ComposedPerm p0, p1;

		auto prepStart = std::chrono::steady_clock::now();
		auto prep = macoro::sync_wait(macoro::when_all_ready(
			g0.start() | macoro::start_on(pool0),
			g1.start() | macoro::start_on(pool1),
			pg0.generate(genSock[0], prng0, Perm(M, prng0), p0) | macoro::start_on(pool0),
			pg1.generate(genSock[1], prng1, Perm(M, prng1), p1) | macoro::start_on(pool1)
		));
		std::get<0>(prep).result(); std::get<1>(prep).result();\n		std::get<2>(prep).result(); std::get<3>(prep).result();
		auto prepEnd = std::chrono::steady_clock::now();
		u64 prepBytes = genSock[0].bytesSent() + genSock[0].bytesReceived()
			+ corSock[0].bytesSent() + corSock[0].bytesReceived();

		oc::Matrix<u8> clear(M, fwdBytes), in0(M, fwdBytes), in1(M, fwdBytes);
		oc::Matrix<u8> sh0(M, fwdBytes), sh1(M, fwdBytes);
		std::memset(clear.data(), 0, clear.size());
		for (u64 i = 0; i < N; ++i)
		{
			clear(i, 0) = i < w;
			u64 z = ((i * 7919 + 17) & ((1ull << 48) - 1));
			if (!z) z = 1;
			for (u64 k = 0; k < 6; ++k) clear(i, 1 + k) = u8(z >> (8 * k));
		}
		for (u64 j = 0; j < B; ++j) clear(N + j, 0) = j < (B - w);
		prng0.get<u8>(in0);
		for (u64 i = 0; i < in0.size(); ++i) in1(i) = in0(i) ^ clear(i);

		auto onlineStart = std::chrono::steady_clock::now();
		auto fwd = macoro::sync_wait(macoro::when_all_ready(
			p0.apply<u8>(PermOp::Regular, in0, sh0, onlineSock[0]) | macoro::start_on(pool0),
			p1.apply<u8>(PermOp::Regular, in1, sh1, onlineSock[1]) | macoro::start_on(pool1)
		));
		std::get<0>(fwd).result(); std::get<1>(fwd).result();

		oc::BitVector fs0(M), fs1(M), peer0(M), peer1(M);
		for (u64 i = 0; i < M; ++i) { fs0[i] = sh0(i,0) & 1; fs1[i] = sh1(i,0) & 1; }
		auto opened = macoro::sync_wait(macoro::when_all_ready(
			onlineSock[0].send(fs0), onlineSock[0].recv(peer0),
			onlineSock[1].send(fs1), onlineSock[1].recv(peer1)
		));
		std::get<0>(opened).result(); std::get<1>(opened).result();\n		std::get<2>(opened).result(); std::get<3>(opened).result();
		fs0 ^= peer0; fs1 ^= peer1;
		if (fs0 != fs1 || fs0.hammingWeight() != B) throw RTE_LOC;

		oc::Matrix<u8> tail0(M, invBytes), tail1(M, invBytes);
		oc::Matrix<u8> back0(M, invBytes), back1(M, invBytes);
		for (u64 i = 0; i < M; ++i)
		{
			for (u64 k = 0; k < 6; ++k)
			{
				tail0(i,k) = fs0[i] ? sh0(i,1+k) : 0;
				tail1(i,k) = fs0[i] ? sh1(i,1+k) : 0;
			}
		}

		auto inv = macoro::sync_wait(macoro::when_all_ready(
			p0.apply<u8>(PermOp::Inverse, tail0, back0, onlineSock[0]) | macoro::start_on(pool0),
			p1.apply<u8>(PermOp::Inverse, tail1, back1, onlineSock[1]) | macoro::start_on(pool1)
		));
		std::get<0>(inv).result(); std::get<1>(inv).result();
		auto onlineEnd = std::chrono::steady_clock::now();

		u64 mismatches = 0;
		for (u64 i = 0; i < N; ++i)
		{
			for (u64 k = 0; k < 6; ++k)
			{
				u8 got = back0(i,k) ^ back1(i,k);
				u8 exp = i < w ? clear(i,1+k) : 0;
				mismatches += got != exp;
			}
		}
		for (u64 j = 0; j < B; ++j)
			for (u64 k = 0; k < 6; ++k)
				mismatches += (back0(N+j,k) ^ back1(N+j,k)) != 0;
		if (mismatches) throw RTE_LOC;

		u64 onlineBytes = onlineSock[0].bytesSent() + onlineSock[0].bytesReceived();
		auto prepMs = std::chrono::duration_cast<std::chrono::microseconds>(prepEnd-prepStart).count()/1000.0;
		auto onlineMs = std::chrono::duration_cast<std::chrono::microseconds>(onlineEnd-onlineStart).count()/1000.0;
		std::cout << "EXP187_RESULT "
			<< "N=" << N << " B=" << B << " w=" << w << " M=" << M
			<< " mock=" << mock
			<< " preprocess_ms=" << prepMs
			<< " preprocess_bytes=" << prepBytes
			<< " online_ms=" << onlineMs
			<< " online_bytes=" << onlineBytes
			<< " online_rounds_model=5"
			<< " opened_weight=" << fs0.hammingWeight()
			<< " mismatches=" << mismatches
			<< std::endl;
	}
'''
    if marker not in s:
        raise SystemExit("benchmark.cpp marker missing")
    s = s.replace(marker, "\n" + fn + marker)
cpp.write_text(s)

h = hdr.read_text()
if "Exp187_shuffle_benchmark" not in h:
    needle = "    void AltModPerm_benchmark(const oc::CLP& cmd);\n"
    if needle not in h:
        raise SystemExit("benchmark.h marker missing")
    h = h.replace(needle, needle + "    void Exp187_shuffle_benchmark(const oc::CLP& cmd);\n")
hdr.write_text(h)

m = main.read_text()
if 'clp.isSet("Exp187")' not in m:
    needle = '''        if (clp.isSet("AltModPerm"))
        {
            AltModPerm_benchmark(clp);
        }
'''
    add = needle + '''        if (clp.isSet("Exp187"))
        {
            Exp187_shuffle_benchmark(clp);
        }
'''
    if needle not in m:
        raise SystemExit("main.cpp marker missing")
    m = m.replace(needle, add)
main.write_text(m)
