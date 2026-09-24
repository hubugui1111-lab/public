#include "NonLinear/relu-ring.h"
#include "OT/emp-ot.h"
#include "utils/net_io_channel.h"
#include <chrono>
#include <cstdint>
#include <thread>
#include <vector>

struct CheetahReluCtx {
  int party;
  int nthreads;
  std::vector<sci::NetIO*> io;
  std::vector<sci::OTPack<sci::NetIO>*> ot;
  std::vector<ReLURingProtocol<sci::NetIO,uint64_t>*> relu;

  CheetahReluCtx(int p,int base_port,const char* ip,int nt)
      :party(p),nthreads(nt),io(nt),ot(nt),relu(nt){
    for(int i=0;i<nthreads;++i){
      io[i]=new sci::NetIO(party==sci::ALICE?nullptr:ip,base_port+i,true);
      const int logical=(i&1)?(3-party):party;
      ot[i]=new sci::OTPack<sci::NetIO>(io[i],logical);
      relu[i]=new ReLURingProtocol<sci::NetIO,uint64_t>(
          logical,RING,io[i],24,MILL_PARAM,ot[i]);
    }
  }
  ~CheetahReluCtx(){
    for(int i=0;i<nthreads;++i){delete relu[i];delete ot[i];delete io[i];}
  }
};

extern "C" __attribute__((visibility("default"))) void* cheetah_relu_create(int party,int base_port,const char* ip,int nthreads){
  try{
    if((party!=sci::ALICE&&party!=sci::BOB)||nthreads<1||nthreads>8)return nullptr;
    return new CheetahReluCtx(party,base_port,ip,nthreads);
  }catch(...){return nullptr;}
}

extern "C" __attribute__((visibility("default"))) int cheetah_relu_apply(void* opaque,const uint64_t* in,uint64_t* out,
                                  int n,int bw,uint64_t* bytes_out,double* ms_out){
  if(!opaque||!in||!out||n<0||bw!=24)return -1;
  auto* ctx=static_cast<CheetahReluCtx*>(opaque);
  // Barrier is outside the measured interval; this removes launch/setup skew.
  uint8_t sync=0;
  if(ctx->party==sci::ALICE){
    ctx->io[0]->send_data(&sync,1);ctx->io[0]->flush();
    ctx->io[0]->recv_data(&sync,1);
  }else{
    ctx->io[0]->recv_data(&sync,1);
    ctx->io[0]->send_data(&sync,1);ctx->io[0]->flush();
  }
  uint64_t before=0;for(auto* x:ctx->io)before+=x->counter;
  auto t0=std::chrono::steady_clock::now();
  std::vector<std::thread> th;th.reserve(ctx->nthreads);
  int off=0,base=n/ctx->nthreads;
  for(int i=0;i<ctx->nthreads;++i){
    int cnt=(i==ctx->nthreads-1)?n-off:base,cur=off;
    th.emplace_back([=]{
      if(cnt>0)ctx->relu[i]->relu(out+cur,const_cast<uint64_t*>(in)+cur,cnt,nullptr,false);
    });
    off+=cnt;
  }
  for(auto& t:th)t.join();
  auto t1=std::chrono::steady_clock::now();
  uint64_t after=0;for(auto* x:ctx->io)after+=x->counter;
  if(bytes_out)*bytes_out=after-before;
  if(ms_out)*ms_out=std::chrono::duration<double,std::milli>(t1-t0).count();
  return 0;
}

extern "C" __attribute__((visibility("default"))) void cheetah_relu_destroy(void* opaque){delete static_cast<CheetahReluCtx*>(opaque);}
