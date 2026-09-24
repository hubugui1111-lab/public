package edu.alibaba.mpc4j.s2pc.aby.pcg.osn.rosn;

import edu.alibaba.mpc4j.common.rpc.pto.AbstractTwoPartyMemoryRpcPto;
import edu.alibaba.mpc4j.common.tool.network.PermutationNetworkUtils;
import edu.alibaba.mpc4j.s2pc.aby.pcg.osn.OsnTestUtils;
import edu.alibaba.mpc4j.s2pc.aby.pcg.osn.rosn.prrs24.Prrs24OprfRosnConfig;
import edu.alibaba.mpc4j.s2pc.pcg.ot.conv32.Conv32Factory.Conv32Type;
import org.junit.Test;

import java.util.concurrent.TimeUnit;

public class Exp191Prrs24RosnBenchTest extends AbstractTwoPartyMemoryRpcPto {
    public Exp191Prrs24RosnBenchTest() {
        super("EXP191_PRRS24_ROSN");
    }

    @Test
    public void testSvode() {
        runMode("SVODE", new Prrs24OprfRosnConfig.Builder(Conv32Type.SVODE).build());
    }

    @Test
    public void testScot() {
        runMode("SCOT", new Prrs24OprfRosnConfig.Builder(Conv32Type.SCOT).build());
    }

    private void runMode(String mode, RosnConfig config) {
        int[][] shapes = new int[][]{
            {3392, 7},
            {3392, 6},
            {3712, 7},
            {3712, 6},
        };
        for (int[] shape : shapes) {
            runOne(mode, config, shape[0], shape[1]);
        }
    }

    private void runOne(String mode, RosnConfig config, int num, int byteLength) {
        RosnSender sender = RosnFactory.createSender(firstRpc, secondRpc.ownParty(), config);
        RosnReceiver receiver = RosnFactory.createReceiver(secondRpc, firstRpc.ownParty(), config);
        sender.setParallel(false);
        receiver.setParallel(false);
        int taskId = Math.abs(SECURE_RANDOM.nextInt());
        sender.setTaskId(taskId);
        receiver.setTaskId(taskId);

        int[] pi = PermutationNetworkUtils.randomPermutation(num, SECURE_RANDOM);
        RosnSenderThread senderThread = new RosnSenderThread(sender, num, byteLength);
        RosnReceiverThread receiverThread = new RosnReceiverThread(receiver, pi, byteLength);

        firstRpc.reset();
        secondRpc.reset();
        long start = System.nanoTime();
        senderThread.start();
        receiverThread.start();
        try {
            senderThread.join();
            receiverThread.join();
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
        long elapsedMs = TimeUnit.NANOSECONDS.toMillis(System.nanoTime() - start);

        RosnSenderOutput senderOutput = senderThread.getSenderOutput();
        RosnReceiverOutput receiverOutput = receiverThread.getReceiverOutput();
        if (senderOutput == null || receiverOutput == null) {
            throw new AssertionError("protocol output missing");
        }
        OsnTestUtils.assertOutput(pi, senderOutput, receiverOutput);

        long senderBytes = firstRpc.getSendByteLength();
        long receiverBytes = secondRpc.getSendByteLength();
        long senderPayload = firstRpc.getPayloadByteLength();
        long receiverPayload = secondRpc.getPayloadByteLength();
        long senderPackets = firstRpc.getSendDataPacketNum();
        long receiverPackets = secondRpc.getSendDataPacketNum();

        System.out.printf(
            "EXP191_RESULT mode=%s num=%d byte_length=%d ms=%d " +
            "sender_bytes=%d receiver_bytes=%d total_bytes=%d " +
            "sender_payload=%d receiver_payload=%d total_payload=%d " +
            "sender_packets=%d receiver_packets=%d total_packets=%d%n",
            mode, num, byteLength, elapsedMs,
            senderBytes, receiverBytes, senderBytes + receiverBytes,
            senderPayload, receiverPayload, senderPayload + receiverPayload,
            senderPackets, receiverPackets, senderPackets + receiverPackets
        );

        new Thread(sender::destroy).start();
        new Thread(receiver::destroy).start();
    }
}
