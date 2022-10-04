This is the Risk-Refinment cycle including the
fully verified application example of the CoronaApp.
It runs with Isabelle 2021-1.
Instructions:
- download current Isabelle from https://isabelle.in.tum.de/
- From this repository Open File CoronaAppThree.thy in the Isabelle file menu
  -> this automatically will load the entire development and case study and run
    The entire case study, that is, check all specifications and proofs.
The directory IsabelleCorona contains:
- DPM2020: the workshop paper (latex sources and pdf version) at DPM2020, co-located with ESORICS, Spinger LNCS 12484, 2020.
- Directory IsabelleCorona with files:
  o MC.thy, AT.thy Modelchecking, Kripke structure and Attack Trees
  o Refinement.thy the RR-cycle
  o Infrastucture*.thy CoronaApp*.thy CoronaWarnAppapllication in three iterations of refinement
  o README.txt, ROOR, directory document Isabelle output generated for readable documentation  
