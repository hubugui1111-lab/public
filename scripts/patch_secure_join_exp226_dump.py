#!/usr/bin/env python3
from pathlib import Path
import sys
root=Path(sys.argv[1]).resolve()
cpp=root/"frontend"/"benchmark.cpp"
hdr=root/"frontend"/"benchmark.h"
main=root/"frontend"/"main.cpp"

s=cpp.read_text()
inc='#include "secure-join/Perm/AltModComposedPerm.h"\n'
if inc not in s:
    s=s.replace('#include "secure-join/Perm/PprfPermGen.h"\n',
                '#include "secure-join/Perm/PprfPermGen.h"\n'+inc)
if '#include <fstream>\n' not in s:
    s=s.replace('#include "secure-join/Perm/AltModComposedPerm.h"\n',
                '#include "secure-join/Perm/AltModComposedPerm.h"\n#include <fstream>\n')

marker="\n\tvoid AltModPerm_benchmark(const oc::CLP& cmd)\n"
if "void Exp226_dump_benchmark" not in s:
    fn=r'''
    void exp226_write_side(
        const std::string& path,
        const ComposedPerm& local,
        const ComposedPerm& peer)
    {
        // local.mPermSender owns this party's permutation/delta.
        // local.mPermReceiver contains A/B for the peer-owned permutation.
        const u32 magic=0x45323236u;
        const u32 M=u32(local.mPermSender.size());
        const u32 bytes=9;
        std::ofstream f(path,std::ios::binary);
        if(!f) throw RTE_LOC;
        f.write((const char*)&magic,4);
        f.write((const char*)&M,4);
        f.write((const char*)&bytes,4);
        f.write((const char*)local.mPermSender.mPerm.mPi.data(),M*4);
        auto write9=[&](const oc::Matrix<oc::block>& mat){
            if(mat.rows()!=M) throw RTE_LOC;
            for(u32 i=0;i<M;++i)
                f.write((const char*)reinterpret_cast<const u8*>(mat.data(i)),bytes);
        };
        write9(local.mPermSender.mDelta);
        write9(local.mPermReceiver.mA);
        write9(local.mPermReceiver.mB);
        f.close();
    }

    void Exp226_dump_benchmark(const oc::CLP& cmd)
    {
        u64 N=cmd.getOr("n",3072ull);
        u64 B=cmd.getOr("B",320ull);
        u64 nt=cmd.getOr("nt",2ull);
        u64 batch=1ull<<cmd.getOr("b",16);
        bool mock=cmd.getOr("mock",0);
        std::string out=cmd.getOr<std::string>("out",".");
        const u64 M=N+B;
        const u64 setupBytes=9; // two 24-bit forward lanes + one 24-bit inverse lane.

        macoro::thread_pool pool0,pool1;
        auto e0=pool0.make_work();auto e1=pool1.make_work();
        pool0.create_threads(nt);pool1.create_threads(nt);
        auto genSock=coproto::LocalAsyncSocket::makePair();
        auto corSock=coproto::LocalAsyncSocket::makePair();
        genSock[0].setExecutor(pool0);corSock[0].setExecutor(pool0);
        genSock[1].setExecutor(pool1);corSock[1].setExecutor(pool1);

        PRNG prng0(oc::sysRandomSeed()),prng1(oc::sysRandomSeed());
        CorGenerator g0,g1;
        g0.init(corSock[0].fork(),prng0,0,nt,batch,mock);
        g1.init(corSock[1].fork(),prng1,1,nt,batch,mock);
        g0.mGenState->mPool=&pool0;g1.mGenState->mPool=&pool1;

        AltModComposedPerm pg0,pg1;
        pg0.init(0,M,setupBytes,g0);
        pg1.init(1,M,setupBytes,g1);
        ComposedPerm p0,p1;
        auto begin=std::chrono::steady_clock::now();
        auto rr=macoro::sync_wait(macoro::when_all_ready(
            g0.start()|macoro::start_on(pool0),
            g1.start()|macoro::start_on(pool1),
            pg0.generate(genSock[0],prng0,Perm(M,prng0),p0)|macoro::start_on(pool0),
            pg1.generate(genSock[1],prng1,Perm(M,prng1),p1)|macoro::start_on(pool1)
        ));
        std::get<0>(rr).result();std::get<1>(rr).result();
        std::get<2>(rr).result();std::get<3>(rr).result();
        auto end=std::chrono::steady_clock::now();
        u64 bytesWire=genSock[0].bytesSent()+genSock[0].bytesReceived()
                     +corSock[0].bytesSent()+corSock[0].bytesReceived();

        exp226_write_side(out+"/exp226_alice.bin",p0,p1);
        exp226_write_side(out+"/exp226_bob.bin",p1,p0);

        auto ms=std::chrono::duration_cast<std::chrono::microseconds>(end-begin).count()/1000.0;
        std::cout<<"EXP226_CORR_RESULT M="<<M<<" setup_bytes="<<setupBytes
                 <<" mock="<<mock<<" preprocess_ms="<<ms
                 <<" preprocess_bytes="<<bytesWire<<std::endl;
    }
'''
    if marker not in s: raise SystemExit("benchmark.cpp marker missing")
    s=s.replace(marker,"\n"+fn+marker)
cpp.write_text(s)

h=hdr.read_text()
if "Exp226_dump_benchmark" not in h:
    needle="    void AltModPerm_benchmark(const oc::CLP& cmd);\n"
    if needle not in h: raise SystemExit("benchmark.h marker missing")
    h=h.replace(needle,needle+"    void Exp226_dump_benchmark(const oc::CLP& cmd);\n")
hdr.write_text(h)

m=main.read_text()
if 'clp.isSet("Exp226")' not in m:
    needle='''        if (clp.isSet("AltModPerm"))
        {
            AltModPerm_benchmark(clp);
        }
'''
    add=needle+'''        if (clp.isSet("Exp226"))
        {
            Exp226_dump_benchmark(clp);
        }
'''
    if needle not in m: raise SystemExit("main.cpp marker missing")
    m=m.replace(needle,add)
main.write_text(m)
