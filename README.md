# machine-certified-linearizability
Contributors: Prasad Jayanti (Dartmouth College), [Siddhartha V. Jayanti](https://github.com/visveswara/) (Google Research), [Uğur Y. Yavuz](https://github.com/uguryavuz/) (Boston University), [Lizzie Hernández Videa](https://github.com/lizziehv) (Microsoft).

## Introduction
This is the artifact package accompanying our POPL 2024 submission titled *A Universal, Sound, and Complete Forward Reasoning Technique for Machine-Verified Proofs of Linearizability.* In the paper, we introduce simple, universal, sound, and complete proof methods for producing machine-verifiable proofs of linearizability and its close cousin, strong linearizability. We demonstrate the simplicity and power of our method by producing proofs of linearizability for the Herlihy-Wing queue and Jayanti's single-scanner snapshot, as well as a proof of strong linearizability of the Jayanti-Tarjan union-find object. We have written and verified our proofs in TLA+/TLAPS,
and these proofs are available in this artifact package, which we provide as a Docker image.

* [proofs/POPL24_Jayanti_SS_Snapshot.tla](https://github.com/uguryavuz/machine-certified-linearizability/blob/main/proofs/POPL24_Jayanti_SS_Snapshot.tla) contains the TLAPS proof for the linearizability of the Jayanti single-scanner snapshot implementation.
* [proofs/POPL24_HerlihyWingQueue.tla](https://github.com/uguryavuz/machine-certified-linearizability/blob/main/proofs/POPL24_HerlihyWingQueue.tla) contains the TLAPS proof for the linearizability of the Herlihy-Wing queue implementation.
    * [proofs/POPL24_HerlihyWingQueuePrelude.tla](https://github.com/uguryavuz/machine-certified-linearizability/blob/main/proofs/POPL24_HerlihyWingQueue.tla) contains TLAPS proofs for a number of lemmas used in the proof of linearizability of the Herlihy-Wing queue implementation.
* [proofs/POPL24_JayantiTarjanUF.tla](https://github.com/uguryavuz/machine-certified-linearizability/blob/main/proofs/POPL24_JayantiTarjanUF.tla) contains the TLAPS proof for the strong linearizability of the Jayanti-Tarjan union-find object implementation.

## Installation

The artifact is provided as a Docker image. To install Docker, please follow the instructions at https://docs.docker.com/get-docker/. Once Docker is installed and the Docker daemon is running, you create the Docker image and run the container as follows:

```bash
git clone https://github.com/uguryavuz/machine-certified-linearizability.git
cd machine-certified-linearizability/docker
docker build -t tlaps-artifact-img .
docker run -it --name tlaps-artifact-cont --platform linux/amd64 tlaps-artifact-img
```

If you ever exit the container and want to re-enter it, you can do so by running the following set of commands:

```bash
docker start tlaps-artifact-cont
docker exec -it tlaps-artifact-cont /bin/bash
```

If you want to remove the container and the image, run the following set of commands:

```bash
docker rm tlaps-artifact-cont
docker rmi tlaps-artifact-img
```

## Usage

Once inside the container, you will be in the `/opt` directory. The artifact is located in the `machine-certified-linearizability` directory, and the proofs are located in  `machine-certified-linearizability/proofs`. `cd` into the proofs directory to verify the proofs.

### Jayanti's single-writer, single-scanner snapshot

To verify the TLAPS proof of the linearizability of Jayanti's single-writer, single-scanner snapshot, run the following set of commands:

```bash
tlapm POPL24_Jayanti_SS_Snapshot.tla --summary
tlapm POPL24_Jayanti_SS_Snapshot.tla --timing --safefp
```

The first command will print a summary of the proof, and will display the number proof obligations, and whether there are any missing or omitted proofs. If the only reported
metric is `obligations_count`, then this means that there are no missing or omitted proofs; otherwise such the number of such proof obligations will be reported. 

The second command will verify the proof, with the help of the proof fingerprints in the `POPL24_Jayanti_SS_Snapshot.tlaps` directory. The `safefp` flag ensures that the versions
of `tlapm` (the command-line tool for TLAPS), `zenon` and `isabelle` (backend provers used by TLAPS) in the container are the same as the versions used to generate the fingerprints, while the `timing` flag will print a report of the time taken for each operation (parsing, analysis, interaction, fingerprint loading, etc.)

### Herlihy-Wing queue

To verify the TLAPS proof of the linearizability of the Herlihy-Wing queue, run the following set of commands:

```bash
tlapm POPL24_HerlihyWingQueuePrelude.tla --summary
tlapm POPL24_HerlihyWingQueuePrelude.tla --timing --safefp
tlapm POPL24_HerlihyWingQueue.tla --summary
tlapm POPL24_HerlihyWingQueue.tla --timing --safefp --stretch 3
```

The first two commands will verify the prelude, which contains a number of lemmas used in the proof of linearizability of the Herlihy-Wing queue. The `stretch` flag in the last command will multiply the default timeout for the proof search (here, it will triple), which is necessary for the proof of linearizability of the Herlihy-Wing queue due to its increased complexity.

### Jayanti-Tarjan union-find

To verify the TLAPS proof of the strong linearizability of the Jayanti-Tarjan union-find object, run the following set of commands:

```bash
tlapm POPL24_JayantiTarjanUF.tla --summary
tlapm POPL24_JayantiTarjanUF.tla --timing --safefp --stretch 3
```

## Evaluation

If all of the above commands succeed, then the proofs are verified. The following table lists the number of proof obligations for each file, and the time taken to verify the proofs when running the containers on two different machines. The first machine is a 2021 MacBook Pro with a 3.2 GHz 10-Core Apple M1 Pro processor and 16 GB of RAM, running macOS Ventura 13.4.1. The second machine is a 2017 MacBook Pro with a 2.5 GHz dual-core Intel Core i7 processor and 16 GB of RAM, running macOS Monterey 12.5.

| File | Obligation Count | Time (M1 Pro) | Time (i7) |
| --- | --- | --- | --- |
| POPL24_Jayanti_SS_Snapshot.tla | 1216 | 7.5s | 13s |
| POPL24_HerlihyWingQueuePrelude.tla | 463 | 14s | 33s |
| POPL24_HerlihyWingQueue.tla | 2496 | 137s | 214s |
| POPL24_JayantiTarjanUF.tla | 3736 | 178s | 244s |
