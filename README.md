# machine-certified-linearizability
Contributors: Prasad Jayanti (Dartmouth College), [Siddhartha V. Jayanti](https://github.com/visveswara/) (Google Research and MIT), [Uğur Y. Yavuz](https://github.com/uguryavuz/) (Boston University), [Lizzie Hernández Videa](https://github.com/lizziehv) (Microsoft).

This repository contains three machine-certified proofs of linearizability that appear in ["A Universal Technique for Machine-Certified Proofs of
Linearizable Algorithms" (arXiv preprint)](https://arxiv.org/abs/2302.00737):
* [proofs/HerlihyWingQueue.tla](https://github.com/uguryavuz/machine-certified-linearizability/blob/main/proofs/HerlihyWingQueue.tla) contains the TLAPS-certified proof for the linearizability of the Herlihy-Wing queue implementation.
* [proofs/POPL24_Jayanti_SS_Snapshot.tla](https://github.com/uguryavuz/machine-certified-linearizability/blob/main/proofs/POPL24_Jayanti_SS_Snapshot.tla) contains the TLAPS-certified proof for the linearizability of the Jayanti single-scanner snapshot implementation.
* [proofs/JayantiTarjanUnionFind.tla](https://github.com/uguryavuz/machine-certified-linearizability/blob/main/proofs/JayantiTarjanUnionFind.tla) contains the TLAPS-certified proof for the strong linearizability of the Jayanti-Tarjan union-find object implementation.
