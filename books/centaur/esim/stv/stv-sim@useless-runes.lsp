(ATOM-LISTP-OF-PAT-FLATTEN1
 (262 62 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (133 11 (:DEFINITION MEMBER-EQUAL))
 (127 2 (:REWRITE SUBSETP-APPEND1))
 (103 7 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (85 6 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (82 82 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (75 7 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (68 3 (:DEFINITION BINARY-APPEND))
 (62 11 (:REWRITE SUBSETP-TRANS2))
 (57 57 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (33 5 (:REWRITE ATOM-LISTP-WHEN-NOT-CONSP))
 (31 28 (:REWRITE SUBSETP-MEMBER . 2))
 (28 28 (:REWRITE SUBSETP-MEMBER . 1))
 (18 2 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (16 16 (:REWRITE DEFAULT-CDR))
 (16 16 (:REWRITE DEFAULT-CAR))
 (11 11 (:REWRITE SUBSETP-TRANS))
 (8 2 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (7 7 (:REWRITE MEMBER-SELF))
 (4 4 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (4 4 (:TYPE-PRESCRIPTION ALISTP))
 (4 2 (:REWRITE CONSP-OF-CAR-WHEN-CONS-LISTP))
 (4 2 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (2 2 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (2 2 (:REWRITE ALISTP-WHEN-ATOM))
 (2 2 (:REWRITE VL2014::ALISTP-WHEN-ALL-HAVE-LEN))
 )
(STV-FULLY-GENERAL-ST-ALIST)
(C0
 (76 38 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (48 3 (:DEFINITION MEMBER-EQUAL))
 (39 9 (:REWRITE DEFAULT-CAR))
 (32 32 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (27 1 (:REWRITE SUBSETP-OF-CONS))
 (26 4 (:REWRITE CONS-LISTP-WHEN-NOT-CONSP))
 (22 22 (:TYPE-PRESCRIPTION PAIRLIS$))
 (19 19 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (15 7 (:REWRITE DEFAULT-CDR))
 (10 10 (:REWRITE CONS-LISTP-WHEN-MEMBER-EQUAL-OF-CONS-LIST-LISTP))
 (7 7 (:REWRITE SUBSETP-MEMBER . 2))
 (7 7 (:REWRITE SUBSETP-MEMBER . 1))
 (3 3 (:REWRITE SUBSETP-TRANS2))
 (3 3 (:REWRITE SUBSETP-TRANS))
 (1 1 (:REWRITE MEMBER-SELF))
 )
(STV-FULLY-GENERAL-IN-ALIST-N
 (110 44 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (52 52 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (43 15 (:REWRITE ATOM-LISTP-WHEN-NOT-CONSP))
 (40 4 (:DEFINITION MEMBER-EQUAL))
 (32 32 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-MEMBER-EQUAL-OF-SYMBOL-LIST-LISTP))
 (27 27 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (27 3 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (19 1 (:REWRITE SUBSETP-OF-CONS))
 (18 18 (:REWRITE DEFAULT-CAR))
 (16 16 (:REWRITE FN-CHECK-DEF-FORMALS))
 (15 15 (:REWRITE DEFAULT-CDR))
 (15 3 (:REWRITE ATOM-LISTP-OF-CDR-WHEN-ATOM-LISTP))
 (14 14 (:REWRITE SUBSETP-MEMBER . 2))
 (14 14 (:REWRITE SUBSETP-MEMBER . 1))
 (7 7 (:REWRITE DEFAULT-<-2))
 (7 7 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE SUBSETP-TRANS2))
 (6 6 (:REWRITE SUBSETP-TRANS))
 (6 6 (:REWRITE MEMBER-SELF))
 (4 2 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 (3 3 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 )
(CONS-LISTP-OF-STV-FULLY-GENERAL-IN-ALIST-N)
(STV-FULLY-GENERAL-IN-ALISTS-AUX
 (12 12 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-MEMBER-EQUAL-OF-SYMBOL-LIST-LISTP))
 (6 6 (:REWRITE FN-CHECK-DEF-FORMALS))
 (6 6 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (6 6 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (3 3 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(CONS-LIST-LISTP-OF-STV-FULLY-GENERAL-IN-ALISTS-AUX
 (64 17 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (55 18 (:REWRITE CONS-LIST-LISTP-WHEN-NOT-CONSP))
 (46 46 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (46 17 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (42 42 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (42 2 (:REWRITE SUBSETP-OF-CONS))
 (24 24 (:REWRITE SUBSETP-TRANS2))
 (24 24 (:REWRITE SUBSETP-TRANS))
 (24 2 (:DEFINITION MEMBER-EQUAL))
 (12 12 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (7 7 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE SUBSETP-MEMBER . 2))
 (4 4 (:REWRITE SUBSETP-MEMBER . 1))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(LEN-STV-FULLY-GENERAL-IN-ALISTS-AUX
 (98 53 (:REWRITE DEFAULT-+-2))
 (57 53 (:REWRITE DEFAULT-+-1))
 (54 54 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (54 54 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (54 54 (:LINEAR LEN-WHEN-PREFIXP))
 (28 22 (:REWRITE DEFAULT-CDR))
 (27 27 (:LINEAR STR::COUNT-LEADING-CHARSET-LEN))
 (24 24 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (24 24 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (7 6 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE DEFAULT-<-2))
 (5 5 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE-QUOTED-CONSTANT FIX-UNDER-NUMBER-EQUIV))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:LINEAR LISTPOS-COMPLETE))
 )
(STV-FULLY-GENERAL-IN-ALISTS)
(CONS-LIST-LISTP-OF-STV-FULLY-GENERAL-IN-ALISTS)
(LEN-STV-FULLY-GENERAL-IN-ALISTS
 (11 1 (:DEFINITION LEN))
 (7 6 (:REWRITE DEFAULT-+-2))
 (6 6 (:REWRITE DEFAULT-+-1))
 (5 5 (:REWRITE DEFAULT-<-2))
 (5 5 (:REWRITE DEFAULT-<-1))
 (5 1 (:REWRITE PAT-FLATTEN1-WHEN-ATOM))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (4 4 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (4 4 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (4 4 (:LINEAR LEN-WHEN-PREFIXP))
 (3 3 (:LINEAR LISTPOS-COMPLETE))
 (2 2 (:TYPE-PRESCRIPTION STV-FULLY-GENERAL-IN-ALISTS-AUX))
 (2 2 (:REWRITE VL2014::POSP-WHEN-MEMBER-EQUAL-OF-POS-LISTP))
 (2 2 (:LINEAR STR::COUNT-LEADING-CHARSET-LEN))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(STV-RUN-ESIM
 (50 50 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (50 50 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (33 17 (:REWRITE DEFAULT-+-2))
 (32 32 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (32 32 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (32 32 (:LINEAR LEN-WHEN-PREFIXP))
 (24 20 (:REWRITE DEFAULT-CDR))
 (17 17 (:REWRITE DEFAULT-+-1))
 (16 16 (:LINEAR STR::COUNT-LEADING-CHARSET-LEN))
 )
(STV-FULLY-GENERAL-SIMULATION-RUN
 (8 8 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-MEMBER-EQUAL-OF-SYMBOL-LIST-LISTP))
 (4 4 (:REWRITE FN-CHECK-DEF-FORMALS))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(STV-RUN-ESIM-DEBUG
 (448 7 (:DEFINITION MOD-INTERNAL-PATHS))
 (245 7 (:DEFINITION COLLECT-SIGNAL-LIST))
 (196 14 (:DEFINITION BINARY-APPEND))
 (196 7 (:REWRITE PAT-FLATTEN-IS-PAT-FLATTEN1))
 (190 190 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (190 190 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (182 28 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (70 14 (:REWRITE PAT-FLATTEN1-WHEN-ATOM))
 (45 41 (:REWRITE DEFAULT-CDR))
 (35 35 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-PAT-FLATTEN1))
 (35 35 (:TYPE-PRESCRIPTION SET-DIFFERENCE-EQUAL))
 (35 7 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 (33 17 (:REWRITE DEFAULT-+-2))
 (32 32 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (32 32 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (32 32 (:LINEAR LEN-WHEN-PREFIXP))
 (21 21 (:REWRITE DEFAULT-CAR))
 (17 17 (:REWRITE DEFAULT-+-1))
 (16 16 (:LINEAR STR::COUNT-LEADING-CHARSET-LEN))
 (7 7 (:REWRITE HONS-SET-DIFF-IS-SET-DIFFERENCE$))
 )
(LEN-OF-STV-RUN-ESIM-DEBUG-0
 (251 14 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (160 14 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (128 128 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (128 128 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (119 7 (:DEFINITION BINARY-APPEND))
 (72 9 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (55 27 (:REWRITE DEFAULT-CDR))
 (49 21 (:REWRITE DEFAULT-CAR))
 (45 9 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (45 9 (:REWRITE ALISTP-WHEN-ATOM))
 (34 2 (:REWRITE ALISTP-OF-CDR))
 (28 28 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (28 28 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (28 28 (:LINEAR LEN-WHEN-PREFIXP))
 (28 14 (:REWRITE CONSP-OF-CAR-WHEN-CONS-LISTP))
 (28 14 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (18 18 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (18 18 (:TYPE-PRESCRIPTION ALISTP))
 (14 14 (:LINEAR STR::COUNT-LEADING-CHARSET-LEN))
 (14 7 (:REWRITE DEFAULT-+-2))
 (9 9 (:REWRITE VL2014::ALISTP-WHEN-ALL-HAVE-LEN))
 (7 7 (:REWRITE DEFAULT-+-1))
 )
(LEN-OF-STV-RUN-ESIM-DEBUG-1
 (251 14 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (160 14 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (128 128 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (128 128 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (119 7 (:DEFINITION BINARY-APPEND))
 (72 9 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (55 27 (:REWRITE DEFAULT-CDR))
 (49 21 (:REWRITE DEFAULT-CAR))
 (45 9 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (45 9 (:REWRITE ALISTP-WHEN-ATOM))
 (34 2 (:REWRITE ALISTP-OF-CDR))
 (28 28 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (28 28 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (28 28 (:LINEAR LEN-WHEN-PREFIXP))
 (28 14 (:REWRITE CONSP-OF-CAR-WHEN-CONS-LISTP))
 (28 14 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (18 18 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (18 18 (:TYPE-PRESCRIPTION ALISTP))
 (14 14 (:LINEAR STR::COUNT-LEADING-CHARSET-LEN))
 (14 7 (:REWRITE DEFAULT-+-2))
 (9 9 (:REWRITE VL2014::ALISTP-WHEN-ALL-HAVE-LEN))
 (7 7 (:REWRITE DEFAULT-+-1))
 )
(LEN-OF-STV-RUN-ESIM-DEBUG-2
 (251 14 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (160 14 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (128 128 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (128 128 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (119 7 (:DEFINITION BINARY-APPEND))
 (72 9 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (55 27 (:REWRITE DEFAULT-CDR))
 (49 21 (:REWRITE DEFAULT-CAR))
 (45 9 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (45 9 (:REWRITE ALISTP-WHEN-ATOM))
 (34 2 (:REWRITE ALISTP-OF-CDR))
 (28 28 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (28 28 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (28 28 (:LINEAR LEN-WHEN-PREFIXP))
 (28 14 (:REWRITE CONSP-OF-CAR-WHEN-CONS-LISTP))
 (28 14 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (18 18 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (18 18 (:TYPE-PRESCRIPTION ALISTP))
 (14 14 (:LINEAR STR::COUNT-LEADING-CHARSET-LEN))
 (14 7 (:REWRITE DEFAULT-+-2))
 (9 9 (:REWRITE VL2014::ALISTP-WHEN-ALL-HAVE-LEN))
 (7 7 (:REWRITE DEFAULT-+-1))
 )
(STV-FULLY-GENERAL-SIMULATION-DEBUG
 (8 8 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-MEMBER-EQUAL-OF-SYMBOL-LIST-LISTP))
 (4 4 (:REWRITE FN-CHECK-DEF-FORMALS))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(LEN-OF-STV-FULLY-GENERAL-SIMULATION-DEBUG-1
 (4 4 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (4 4 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (4 4 (:LINEAR LEN-WHEN-PREFIXP))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:LINEAR STR::COUNT-LEADING-CHARSET-LEN))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:LINEAR LISTPOS-COMPLETE))
 )
(LEN-OF-STV-FULLY-GENERAL-SIMULATION-DEBUG-2
 (4 4 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (4 4 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (4 4 (:LINEAR LEN-WHEN-PREFIXP))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:LINEAR STR::COUNT-LEADING-CHARSET-LEN))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:LINEAR LISTPOS-COMPLETE))
 )
(LEN-OF-STV-FULLY-GENERAL-SIMULATION-DEBUG-3
 (4 4 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (4 4 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (4 4 (:LINEAR LEN-WHEN-PREFIXP))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:LINEAR STR::COUNT-LEADING-CHARSET-LEN))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:LINEAR LISTPOS-COMPLETE))
 )
(LEN-OF-STV-FULLY-GENERAL-SIMULATION-DEBUG-4
 (4 4 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (4 4 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (4 4 (:LINEAR LEN-WHEN-PREFIXP))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:LINEAR STR::COUNT-LEADING-CHARSET-LEN))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:LINEAR LISTPOS-COMPLETE))
 )
(CONS-LIST-LISTP-OF-STV-FULLY-GENERAL-SIMULATION-DEBUG-1
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(STV-EXTRACT-RELEVANT-SIGNALS
 (20 2 (:REWRITE ACL2-COUNT-WHEN-MEMBER))
 (12 2 (:DEFINITION MEMBER-EQUAL))
 (8 8 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE SUBSETP-MEMBER . 2))
 (4 4 (:REWRITE SUBSETP-MEMBER . 1))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (4 2 (:REWRITE DEFAULT-<-2))
 (4 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (2 2 (:REWRITE MEMBER-SELF))
 (2 2 (:REWRITE DEFAULT-CAR))
 )
(STV-PROCESS
 (12 6 (:TYPE-PRESCRIPTION RETURN-TYPE-OF-COMPILED-STV->OUT-EXTRACT-ALISTS))
 (12 6 (:TYPE-PRESCRIPTION RETURN-TYPE-OF-COMPILED-STV->NST-EXTRACT-ALISTS))
 )
(RETURN-TYPE-OF-STV-PROCESS
 (147 2 (:DEFINITION 4V-SEXPR-RESTRICT-WITH-RW-ALIST))
 (74 2 (:DEFINITION 4V-SEXPR-RESTRICT-WITH-RW))
 (47 4 (:REWRITE PROCESSED-STV-P-WHEN-WRONG-TAG))
 (44 2 (:DEFINITION SEXPR-REWRITE-FNCALL))
 (42 3 (:REWRITE SUBSETP-CONS-2))
 (33 6 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (32 32 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (32 32 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (30 28 (:REWRITE HONS-ASSOC-EQUAL-OF-CONS))
 (25 6 (:REWRITE TAG-WHEN-PROCESSED-STV-P))
 (24 3 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (24 3 (:DEFINITION ATOM))
 (23 2 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (21 3 (:REWRITE COMPILED-STV-P-WHEN-WRONG-TAG))
 (20 12 (:REWRITE DEFAULT-CDR))
 (17 4 (:REWRITE TAG-WHEN-STVDATA-P))
 (17 4 (:REWRITE TAG-WHEN-COMPILED-STV-P))
 (15 15 (:TYPE-PRESCRIPTION STV-EXTRACT-RELEVANT-SIGNALS))
 (12 4 (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
 (12 2 (:DEFINITION HONS-GET))
 (10 10 (:REWRITE DEFAULT-CAR))
 (8 2 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (6 6 (:REWRITE SUBSETP-TRANS2))
 (6 6 (:REWRITE SUBSETP-TRANS))
 (4 4 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (4 4 (:TYPE-PRESCRIPTION BOOLEANP-OF-STVDATA-P))
 (4 4 (:TYPE-PRESCRIPTION ALISTP))
 (4 2 (:REWRITE CONSP-OF-CAR-WHEN-CONS-LISTP))
 (4 2 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (3 3 (:REWRITE SUBSETP-EQUAL-BAD-GUY))
 (2 2 (:TYPE-PRESCRIPTION HONS-ASSOC-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION CONS-LISTP))
 (2 2 (:TYPE-PRESCRIPTION ATOM-LISTP))
 (2 2 (:REWRITE TAG-OF-PROCESSED-STV))
 (2 2 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (2 2 (:REWRITE ALISTP-WHEN-ATOM))
 (2 2 (:REWRITE VL2014::ALISTP-WHEN-ALL-HAVE-LEN))
 (2 2 (:DEFINITION HONS))
 )
