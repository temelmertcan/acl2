(SYMBOL-BINARY-APPEND)
(GET-FN)
(SET-FN)
(NEXT-VAR)
(GET-FNS)
(REG-VARS)
(VAR-BINDS)
(LOGIC-FN)
(LOGIC-FNS)
(SV-BINDS)
(SV-NEXTS)
(SV-UPDATES)
(INV-UNR)
(LGC-FNCLS)
(VAR-NILS)
(GET-FNCLS)
(INIT-UPDS)
(OPEN-INIT-THMS)
(OPEN-STEP-THMS)
(INITIAL-PC)
(INITIAL-RA)
(INITIAL-RB)
(INSTR)
(>N)
(+N)
(RPC)
(STEP-SV)
(INIT-SV)
(RUN-SV)
(RUN-STATE)
(INV)
(OPEN-INIT-RPC
 (1 1 (:REWRITE ZP-OPEN))
 )
(OPEN-INIT-RRA
 (1 1 (:REWRITE ZP-OPEN))
 )
(OPEN-INIT-RRB
 (1 1 (:REWRITE ZP-OPEN))
 )
(OPEN-STEP-RPC
 (243 44 (:REWRITE ZP-OPEN))
 (105 14 (:REWRITE OPEN-INIT-RPC))
 (88 11 (:REWRITE OPEN-INIT-RRB))
 (88 11 (:REWRITE OPEN-INIT-RRA))
 (86 2 (:DEFINITION RRB))
 (80 2 (:DEFINITION RRA))
 (78 78 (:REWRITE DEFAULT-<-2))
 (78 78 (:REWRITE DEFAULT-<-1))
 (72 24 (:REWRITE FOLD-CONSTS-IN-+))
 (35 35 (:REWRITE DEFAULT-+-2))
 (35 35 (:REWRITE DEFAULT-+-1))
 (2 2 (:TYPE-PRESCRIPTION >N))
 )
(OPEN-STEP-RRA
 (227 41 (:REWRITE ZP-OPEN))
 (89 12 (:REWRITE OPEN-INIT-RRA))
 (86 2 (:DEFINITION RRB))
 (84 2 (:DEFINITION RPC))
 (80 10 (:REWRITE OPEN-INIT-RRB))
 (80 10 (:REWRITE OPEN-INIT-RPC))
 (73 73 (:REWRITE DEFAULT-<-2))
 (73 73 (:REWRITE DEFAULT-<-1))
 (63 21 (:REWRITE FOLD-CONSTS-IN-+))
 (31 31 (:REWRITE DEFAULT-+-2))
 (31 31 (:REWRITE DEFAULT-+-1))
 (16 2 (:REWRITE OPEN-STEP-RPC))
 (2 2 (:TYPE-PRESCRIPTION >N))
 )
(OPEN-STEP-RRB
 (307 55 (:REWRITE ZP-OPEN))
 (126 3 (:DEFINITION RPC))
 (120 3 (:DEFINITION RRA))
 (105 14 (:REWRITE OPEN-INIT-RRB))
 (104 13 (:REWRITE OPEN-INIT-RRA))
 (104 13 (:REWRITE OPEN-INIT-RPC))
 (99 99 (:REWRITE DEFAULT-<-2))
 (99 99 (:REWRITE DEFAULT-<-1))
 (81 27 (:REWRITE FOLD-CONSTS-IN-+))
 (39 39 (:REWRITE DEFAULT-+-2))
 (39 39 (:REWRITE DEFAULT-+-1))
 (24 3 (:REWRITE OPEN-STEP-RRA))
 (24 3 (:REWRITE OPEN-STEP-RPC))
 )
(INV-OVER-STEP-SV
 (121 16 (:REWRITE OPEN-INIT-RRB))
 (121 16 (:REWRITE OPEN-INIT-RRA))
 (121 16 (:REWRITE OPEN-INIT-RPC))
 (120 120 (:REWRITE DEFAULT-<-2))
 (120 120 (:REWRITE DEFAULT-<-1))
 (48 48 (:REWRITE DEFAULT-+-2))
 (48 48 (:REWRITE DEFAULT-+-1))
 (36 36 (:REWRITE DEFAULT-CDR))
 (18 18 (:REWRITE DEFAULT-CAR))
 )
(INV-OF-INIT-SV
 (33 33 (:REWRITE DEFAULT-CDR))
 (9 9 (:REWRITE DEFAULT-CAR))
 )
(RUN-SV-COMMUTE
 (15 6 (:REWRITE DEFAULT-CDR))
 (15 6 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 )
(INDUCT-SCHEME)
(INV-OVER-RUN-SV
 (62 62 (:REWRITE DEFAULT-+-2))
 (62 62 (:REWRITE DEFAULT-+-1))
 (54 54 (:REWRITE DEFAULT-<-2))
 (54 54 (:REWRITE DEFAULT-<-1))
 )
(INV-OVER-RUN-STATE
 (414 2 (:DEFINITION RUN-SV))
 (406 2 (:DEFINITION STEP-SV))
 (350 12 (:DEFINITION UPDATE-NTH))
 (254 2 (:DEFINITION UPDATE-R-RRB))
 (192 48 (:DEFINITION NTH))
 (160 160 (:TYPE-PRESCRIPTION INIT-SV))
 (146 68 (:REWRITE DEFAULT-CDR))
 (94 2 (:DEFINITION UPDATE-R-RRA))
 (68 34 (:REWRITE DEFAULT-CAR))
 (52 52 (:TYPE-PRESCRIPTION INSTR))
 (10 2 (:DEFINITION R-RRB))
 (10 2 (:DEFINITION R-RRA))
 (10 2 (:DEFINITION R-RPC))
 (8 2 (:DEFINITION UPDATE-R-RPC))
 (6 6 (:TYPE-PRESCRIPTION >N))
 (6 6 (:REWRITE CDR-CONS))
 (6 6 (:REWRITE CAR-CONS))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(INV-UNROLL)
(MACHINE-STATE)
(MACHINE-STATE-GUARD-IMPLIES-TEST)
(MACHINE-STATE
 (126 36 (:REWRITE ZP-OPEN))
 (74 2 (:DEFINITION RRB))
 (72 2 (:DEFINITION RPC))
 (68 2 (:DEFINITION RRA))
 (56 8 (:REWRITE OPEN-INIT-RRB))
 (56 8 (:REWRITE OPEN-INIT-RRA))
 (56 8 (:REWRITE OPEN-INIT-RPC))
 (42 42 (:TYPE-PRESCRIPTION ZP))
 (37 37 (:REWRITE DEFAULT-<-2))
 (37 37 (:REWRITE DEFAULT-<-1))
 (18 18 (:REWRITE DEFAULT-+-2))
 (18 18 (:REWRITE DEFAULT-+-1))
 (16 16 (:TYPE-PRESCRIPTION INSTR))
 (8 2 (:REWRITE OPEN-STEP-RRB))
 (8 2 (:REWRITE OPEN-STEP-RRA))
 (8 2 (:REWRITE OPEN-STEP-RPC))
 (2 2 (:TYPE-PRESCRIPTION >N))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
