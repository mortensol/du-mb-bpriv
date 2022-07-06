# Delay-use malicious-ballotbox ballot privacy for Selene

This repository contains the EasyCrypt code associated with the paper "Machine-checked proofs of privacy against
malicious boards for Selene & Co". The main contribution of the paper is a new definition of ballot privacy for electronic voting systems, called *delay-use malicious-ballotbox ballot privacy* (or *du-mb-bpriv*), assuming a dishonest ballot box and allowing for delayed use of voter verification (i.e. voter verification can happen after the tally has been computed).  As a case study, we prove that [Selene](https://eprint.iacr.org/2015/1105.pdf), [Labelled-MiniVoting](https://hal.inria.fr/hal-01624270/document) and [Belenios](https://www.belenios.org/) all satisfy this definition of ballot privacy.

In addition, we model the [*mb-bpriv* ballot privacy definition](https://eprint.iacr.org/2020/127.pdf) in EasyCrypt, and prove that Labelled-MiniVoting and Belenios satisfy this definition.

#### Contents
  * The [`Core`](https://github.com/mortensol/du-mb-bpriv/tree/main/Core) folder contains files modelling labelled public key encryption systems (including a concrete model of the ElGamal PKE), zero-knowledge proof systems and hybrid arguments
  * The [`du_mb_bpriv`](https://github.com/mortensol/du-mb-bpriv/tree/main/du_mb_bpriv) folder contains:
    * A definition of voting systems and the du-mb-bpriv security definition ([`du_mb_bpriv/VotingDefinition`](https://github.com/mortensol/du-mb-bpriv/tree/main/du_mb_bpriv/VotingDefinition))
    * A proof that the Selene voting protocol satisfies du-mb-bpriv (Selene with signatures in [`du_mb_bpriv/Selene_with_signatures`](https://github.com/mortensol/du-mb-bpriv/tree/main/du_mb_bpriv/Selene_with_signatures) and Selene without signatures in [`du_mb_bpriv/Selene`](https://github.com/mortensol/du-mb-bpriv/tree/main/du_mb_bpriv/Selene))
    * Proofs that Labelled-MiniVoting and Belenios satisfy du-mb-bpriv ([`du_mb_bpriv/Belenios_and_MiniVoting`](https://github.com/mortensol/du-mb-bpriv/tree/main/du_mb_bpriv/Belenios_and_MiniVoting))
  *  The [`mb_bpriv_orignal_def`](https://github.com/mortensol/du-mb-bpriv/tree/main/mb_bpriv_original_def) folder contains an EasyCrypt model of the mb-bpriv ballot privacy definition and proofs that Labelled-MiniVoting and Belenios satisfy this definition

#### Installing EasyCrypt
We refer to https://github.com/EasyCrypt/easycrypt for instructions on how to install EasyCrypt.
This proof is known to check with EasyCrypt stable release `r2022.04`, using Z3 4.8.10, Alt-Ergo 2.4.1, and CVC4 1.8.
