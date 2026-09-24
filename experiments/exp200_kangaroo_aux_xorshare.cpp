#include <seal/seal.h>
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <random>
#include <sstream>
#include <vector>

using namespace seal;
using Clock = std::chrono::steady_clock;

static int64_t centered(uint64_t x, uint64_t t) {
    return x > t/2 ? int64_t(x) - int64_t(t) : int64_t(x);
}
static uint64_t mod_i64(int64_t x, uint64_t t) {
    __int128 v=x, m=t;
    v%=m; if(v<0) v+=m;
    return uint64_t(v);
}

int main() {
    constexpr size_t DEG=8192;
    constexpr size_t ACTIVE=6160; // 15 probes + 6144 certificate inequalities + 1 overflow
    EncryptionParameters parms(scheme_type::bfv);
    parms.set_poly_modulus_degree(DEG);
    parms.set_coeff_modulus(CoeffModulus::BFVDefault(DEG));
    parms.set_plain_modulus(PlainModulus::Batching(DEG,50));
    SEALContext context(parms);
    if(!context.parameters_set()) {
        std::cerr<<"EXP200_ERROR context\n"; return 2;
    }
    BatchEncoder encoder(context);
    KeyGenerator keygen(context);
    SecretKey sk=keygen.secret_key();
    PublicKey pk; keygen.create_public_key(pk);
    Encryptor enc(context,pk);
    Evaluator eval(context);
    Decryptor dec(context,sk);
    const uint64_t t=parms.plain_modulus().value();

    std::mt19937_64 rng(0x20020260924ULL);
    std::uniform_int_distribution<int64_t> dd(-(1LL<<20),(1LL<<20));
    std::uniform_int_distribution<uint64_t> ur(0,t-1);

    std::vector<int64_t> clear(DEG,0);
    // Deterministic edge coverage first.
    const std::vector<int64_t> edges={
        0,1,-1,2,-2,4095,-4095,(1LL<<20),-(1LL<<20)
    };
    for(size_t i=0;i<edges.size();++i) clear[i]=edges[i];
    for(size_t i=edges.size();i<ACTIVE;++i) clear[i]=dd(rng);

    // Two additive shares mod t. Neither party alone has d.
    std::vector<uint64_t> cshare(DEG), sshare(DEG);
    for(size_t i=0;i<DEG;++i){
        cshare[i]=ur(rng);
        sshare[i]=(mod_i64(clear[i],t)+t-cshare[i])%t;
    }

    Plaintext pc;
    auto t0=Clock::now();
    encoder.encode(cshare,pc);
    Ciphertext ct;
    enc.encrypt(pc,ct);
    auto t1=Clock::now();

    // Serialized client->server bytes.
    std::stringstream ss_in;
    size_t c2s=ct.save(ss_in);

    // Server reconstructs only under encryption.
    Plaintext ps;
    encoder.encode(sshare,ps);
    eval.add_plain_inplace(ct,ps);

    // Kangaroo-style affine order blinding:
    // V = R * (A*d + B), A>B>0, R in {+1,-1}.
    // For integer d, sign(A*d+B) == [d>=0].
    std::vector<uint64_t> mult(DEG,1), add(DEG,0);
    std::vector<uint8_t> flip(DEG,0);
    uint64_t max_abs_blind=0;
    for(size_t i=0;i<ACTIVE;++i){
        uint64_t A=2+(rng()%1023);        // [2,1024]
        uint64_t B=1+(rng()%(A-1));       // [1,A-1]
        bool neg=(rng()&1)!=0;
        flip[i]=uint8_t(neg);
        int64_t r=neg?-1:1;
        int64_t m=r*int64_t(A);
        int64_t a=r*int64_t(B);
        mult[i]=mod_i64(m,t);
        add[i]=mod_i64(a,t);
        __int128 v=__int128(A)*clear[i]+B;
        if(v<0) v=-v;
        if(v>max_abs_blind) max_abs_blind=uint64_t(v);
        if(v>=__int128(t/2)){
            std::cerr<<"EXP200_ERROR wrap-risk slot="<<i<<"\n"; return 3;
        }
    }
    Plaintext pm,pa;
    encoder.encode(mult,pm); encoder.encode(add,pa);
    auto t2=Clock::now();
    eval.multiply_plain_inplace(ct,pm);
    eval.add_plain_inplace(ct,pa);
    auto t3=Clock::now();

    std::stringstream ss_out;
    size_t s2c=ct.save(ss_out);

    // Client decrypts blinded values and does ordinary plaintext sign tests.
    Plaintext pv;
    dec.decrypt(ct,pv);
    std::vector<uint64_t> blinded;
    encoder.decode(pv,blinded);
    std::vector<uint8_t> client_share(ACTIVE), recovered(ACTIVE);
    size_t masked_eq_true=0, ones=0;
    auto t4=Clock::now();
    for(size_t i=0;i<ACTIVE;++i){
        int64_t v=centered(blinded[i],t);
        client_share[i]=uint8_t(v>=0);
        recovered[i]=uint8_t(client_share[i]^flip[i]);
        const uint8_t truth=uint8_t(clear[i]>=0);
        if(client_share[i]==truth) ++masked_eq_true;
        ones+=client_share[i];
        if(recovered[i]!=truth){
            std::cerr<<"EXP200_ERROR mismatch slot="<<i<<" d="<<clear[i]
                     <<" c="<<int(client_share[i])<<" f="<<int(flip[i])<<"\n";
            return 4;
        }
    }
    auto t5=Clock::now();

    const double enc_ms=std::chrono::duration<double,std::milli>(t1-t0).count();
    const double server_ms=std::chrono::duration<double,std::milli>(t3-t2).count();
    const double client_ms=std::chrono::duration<double,std::milli>(t5-t4).count();
    std::cout<<"EXP200_RESULT"
             <<" slots="<<DEG
             <<" active="<<ACTIVE
             <<" plaintext_bits=50"
             <<" c2s_bytes="<<c2s
             <<" s2c_bytes="<<s2c
             <<" total_online_bytes="<<(c2s+s2c)
             <<" online_round_trips=1"
             <<" client_encrypt_ms="<<enc_ms
             <<" server_blind_eval_ms="<<server_ms
             <<" client_decrypt_compare_ms="<<client_ms
             <<" max_abs_blinded="<<max_abs_blind
             <<" centered_half_modulus="<<(t/2)
             <<" xor_share_mismatches=0"
             <<" client_share_ones="<<ones
             <<" client_share_equals_true="<<masked_eq_true
             <<"\n";
    return 0;
}
