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
    s=s.replace('#include <iostream>\n','#include <iostream>\n#include <fstream>\n')

marker="\n\tvoid AltModPerm_benchmark(const oc::CLP& cmd)\n"
if "void Exp224_export_perm_corr" not in s:
    fn=r'''
    static void exp224_write_party(const std::string& path, const ComposedPerm& cp, u64 bytesPerRow)
    {
        std::ofstream os(path, std::ios::binary);
        if(!os) throw RTE_LOC;
        const char magic[8]={'E','2','2','4','X','O','R','1'};
        os.write(magic,8);
        u32 m=(u32)cp.size(), bpr=(u32)bytesPerRow;
        os.write((char*)&m,4);os.write((char*)&bpr,4);

        // Own secret permutation.
        const auto& pi=cp.mPermSender.mPerm.mPi;
        if(pi.size()!=m) throw RTE_LOC;
        for(u64 i=0;i<m;++i){u32 v=(u32)pi[i];os.write((char*)&v,4);}

        auto writeRows=[&](const oc::Matrix<oc::block>& mat){
            if(mat.rows()!=m) throw RTE_LOC;
            auto bytes=matrixCast<const u8>(mat);
            if(bytes.cols()<bytesPerRow) throw RTE_LOC;
            for(u64 i=0;i<m;++i) os.write((char*)bytes.data(i),bytesPerRow);
        };
        // Sender material for own permutation, receiver material for peer's.
        writeRows(cp.mPermSender.mDelta);
        writeRows(cp.mPermReceiver.mA);
        writeRows(cp.mPermReceiver.mB);
        if(!os) throw RTE_LOC;
    }

    void Exp224_export_perm_corr(const oc::CLP& cmd)
    {
        u64 N=cmd.getOr("n",3072ull);
        u64 B=cmd.getOr("B",320ull);
        u64 nt=cmd.getOr("nt",2ull);
        u64 batch=1ull<<cmd.getOr("b",16);
        bool mock=cmd.getOr("mock",0);
        std::string out0=cmd.getOr("out0",std::string("exp224_xor_p0.bin"));
        std::string out1=cmd.getOr("out1",std::string("exp224_xor_p1.bin"));
        const u64 M=N+B, setupBytes=9; // two 24-bit forward words + one inverse word.

        macoro::thread_pool pool0,pool1;
        auto e0=pool0.make_work();auto e1=pool1.make_work();
        pool0.create_threads(nt);pool1.create_threads(nt);

        auto genSock=coproto::LocalAsyncSocket::makePair();
        auto corSock=coproto::LocalAsyncSocket::makePair();
        for(auto*p:{&genSock[0],&corSock[0]})p->setExecutor(pool0);
        for(auto*p:{&genSock[1],&corSock[1]})p->setExecutor(pool1);

        PRNG prng0(oc::ZeroBlock),prng1(oc::OneBlock);
        CorGenerator g0,g1;
        g0.init(corSock[0].fork(),prng0,0,nt,batch,mock);
        g1.init(corSock[1].fork(),prng1,1,nt,batch,mock);
        g0.mGenState->mPool=&pool0;g1.mGenState->mPool=&pool1;

        AltModComposedPerm pg0,pg1;
        pg0.init(0,M,setupBytes,g0);
        pg1.init(1,M,setupBytes,g1);
        ComposedPerm p0,p1;

        auto start=std::chrono::steady_clock::now();
        auto all=macoro::sync_wait(macoro::when_all_ready(
            g0.start()|macoro::start_on(pool0),
            g1.start()|macoro::start_on(pool1),
            pg0.generate(genSock[0],prng0,Perm(M,prng0),p0)|macoro::start_on(pool0),
            pg1.generate(genSock[1],prng1,Perm(M,prng1),p1)|macoro::start_on(pool1)
        ));
        std::get<0>(all).result();std::get<1>(all).result();
        std::get<2>(all).result();std::get<3>(all).result();
        auto end=std::chrono::steady_clock::now();

        exp224_write_party(out0,p0,setupBytes);
        exp224_write_party(out1,p1,setupBytes);

        u64 bytes=genSock[0].bytesSent()+genSock[0].bytesReceived()
            +corSock[0].bytesSent()+corSock[0].bytesReceived();
        double ms=std::chrono::duration_cast<std::chrono::microseconds>(end-start).count()/1000.0;
        std::cout<<"EXP224_XOR_PREP_RESULT N="<<N<<" B="<<B<<" M="<<M
            <<" setup_bytes_per_row="<<setupBytes<<" mock="<<mock
            <<" preprocess_ms="<<ms<<" preprocess_bytes="<<bytes
            <<" out0="<<out0<<" out1="<<out1<<std::endl;
    }
'''
    if marker not in s: raise SystemExit("benchmark marker missing")
    s=s.replace(marker,"\n"+fn+marker)
cpp.write_text(s)

h=hdr.read_text()
if "Exp224_export_perm_corr" not in h:
    needle="    void AltModPerm_benchmark(const oc::CLP& cmd);\n"
    if needle not in h: raise SystemExit("header marker missing")
    h=h.replace(needle,needle+"    void Exp224_export_perm_corr(const oc::CLP& cmd);\n")
hdr.write_text(h)

m=main.read_text()
if 'clp.isSet("Exp224")' not in m:
    needle='''        if (clp.isSet("AltModPerm"))
        {
            AltModPerm_benchmark(clp);
        }
'''
    add=needle+'''        if (clp.isSet("Exp224"))
        {
            Exp224_export_perm_corr(clp);
        }
'''
    if needle not in m: raise SystemExit("main marker missing")
    m=m.replace(needle,add)
main.write_text(m)
