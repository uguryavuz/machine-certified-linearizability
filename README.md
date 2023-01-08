# machine-certified-linearizability
Contributors: Prasad Jayanti (Dartmouth College), [Siddhartha V. Jayanti](https://github.com/visveswara/) (Google Research and MIT), [Ugur Y. Yavuz](https://github.com/uguryavuz/) (Boston University), [Lizzie Hernández Videa](https://github.com/lizziehv) (Microsoft).

This repository contains three machine-certified proofs of linearizability that appear in "A Univeral Technique for Machine-Certified Proofs of
Linearizable Algorithms":
* [HerlihyWingQueue.tla](https://github.com/uguryavuz/machine-certified-linearizability/blob/main/HerlihyWingQueue.tla) contains the TLAPS-certified proof for the linearizability of the Herlihy-Wing queue implementation.
* [JayantiSingleScannerSnapshot.tla](https://github.com/uguryavuz/machine-certified-linearizability/blob/main/JayantiSingleScannerSnapshot.tla) contains the TLAPS-certified proof for the linearizability of the Jayanti single-scanner snapshot implementation.
* [JayantiTarjanUnionFind.tla](https://github.com/uguryavuz/machine-certified-linearizability/blob/main/JayantiTarjanUnionFind.tla) contains the TLAPS-certified proof for the strong linearizability of the Jayanti-Tarjan union-find object implementation.
