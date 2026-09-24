#!/usr/bin/env python3
from pathlib import Path
import sys
root=Path(sys.argv[1])
p=root/"secure-join/Perm/PprfPermGen.h"
s=p.read_text()
s=s.replace(
"auto base = std::vector<std::array<block, 2>>(mSender.baseOtCount());",
"auto base = oc::AlignedUnVector<std::array<block, 2>>(mSender.baseOtCount());")
s=s.replace(
"auto base = std::vector<block>(mRecver.baseOtCount());",
"auto base = oc::AlignedUnVector<block>(mRecver.baseOtCount());")
p.write_text(s)
