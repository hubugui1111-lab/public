#include <emp-sh2pc/emp-sh2pc.h>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>

using namespace emp;

template<int B, int K>
int run_case(int party, int w) {
    using Ctx = SH2PCSession::ctx_t;
    using U16 = UInt_T<Ctx,16>;
    using Bit = Bit_T<Ctx>;
    using BV = BitVec_T<Ctx,B>;

    if (w < 0 || w > 3072) return 2;
    const int port = peer_port();
    auto io = (party == ALICE) ? NetIO::listen(port) : NetIO::connect(peer_ip(), port);

    const uint64_t send0 = io->send_counter;
    const uint64_t recv0 = io->recv_counter;
    const auto t0 = std::chrono::steady_clock::now();

    SH2PCSession sess(io.get(), party);

    const uint16_t alice_share = 0x1234u;
    const uint16_t bob_share = uint16_t(uint32_t(w) - uint32_t(alice_share));
    U16 a = sess.input<U16>(ALICE, party == ALICE ? alice_share : 0);
    U16 b = sess.input<U16>(BOB,   party == BOB   ? bob_share   : 0);
    U16 count = a + b;
    U16 cap = U16::constant(sess.ctx(), B);
    Bit accepted = count <= cap;
    U16 need = cap - count;

    std::vector<Bit> onehot;
    onehot.push_back(Bit::constant(sess.ctx(), true));
    for (int bit=0; bit<K; ++bit) {
        Bit x(sess.ctx(), need.w[bit]);
        const size_t old = onehot.size();
        std::vector<Bit> next(2*old);
        for (size_t i=0;i<old;++i) {
            Bit high = onehot[i] & x;
            next[i] = onehot[i] ^ high;
            next[i+old] = high;
        }
        onehot = std::move(next);
    }

    std::vector<Bit> dummy(B);
    Bit suffix = Bit::constant(sess.ctx(), false);
    for (int j=int(onehot.size())-2; j>=0; --j) {
        suffix = suffix ^ onehot[j+1];
        if (j < B) dummy[j] = suffix;
    }
    BV out = BV::from_bit_values(sess.ctx(), dummy.data());

    auto xor_share_opt = sess.reveal(out, XOR);
    auto accepted_opt = sess.reveal(accepted, PUBLIC);
    sess.finalize();

    const auto t1 = std::chrono::steady_clock::now();
    const uint64_t protocol_bytes =
        (io->send_counter - send0) + (io->recv_counter - recv0);
    const double ms = std::chrono::duration<double,std::milli>(t1-t0).count();

    if (!xor_share_opt || !accepted_opt) return 3;
    auto xor_share = xor_share_opt.value();
    std::vector<uint8_t> mine(B), peer(B);
    for (int j=0;j<B;++j) mine[j]=uint8_t(xor_share[j]);
    if (party == ALICE) {
        io->send_data(mine.data(), mine.size()); io->flush();
        io->recv_data(peer.data(), peer.size());
    } else {
        io->recv_data(peer.data(), peer.size());
        io->send_data(mine.data(), mine.size()); io->flush();
    }

    const bool acc = accepted_opt.value();
    int mismatches=0, weight=0;
    for (int j=0;j<B;++j) {
        const bool d = bool(mine[j]^peer[j]);
        weight += d;
        if (acc) mismatches += d != (j < (B-w));
    }
    mismatches += acc != (w <= B);

    std::cout
      << "EXP192_RESULT party=" << party
      << " B=" << B << " w=" << w
      << " accepted=" << int(acc)
      << " dummy_weight=" << weight
      << " protocol_bytes=" << protocol_bytes
      << " protocol_ms=" << ms
      << " decoder_ands=" << ((1<<K)-1)
      << " mismatches=" << mismatches
      << std::endl;
    return mismatches ? 4 : 0;
}

int main(int argc, char** argv) {
    if (argc != 4) return 1;
    int party = parse_party(argv);
    int B = std::atoi(argv[2]);
    int w = std::atoi(argv[3]);
    if (B == 320) return run_case<320,9>(party,w);
    if (B == 640) return run_case<640,10>(party,w);
    return 5;
}
