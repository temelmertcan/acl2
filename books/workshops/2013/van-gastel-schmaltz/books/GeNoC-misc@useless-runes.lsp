(NIL_LIST)
(NOT-IN-TEST
 (10 5 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (5 5 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(NOT-IN-TEST-FOR-ALL-PREDICATE)
(NOT-IN)
(NOT-IN-TEST-FOR-ALL-HOLDS-FOR-MEMBER)
(NOT-IN-TEST-PERMP-IMPLIES-EQUAL-FOR-ALL-1)
(NOT-IN-TEST-FOR-ALL-HOLDS-FOR-ASSOC)
(NOT-IN-TEST-FOR-ALL-REMOVING-MEMBER)
(NOT-IN-TEST-FOR-ALL-APPEND)
(NOT-IN-TEST-FOR-ALL-SUBSET)
(NOT-IN-TEST-FOR-ALL-SUBSET-APPEND)
(NOT-IN-TEST-FOR-ALL-CDR)
(PERMP-IMPLIES-EQUAL-NOT-IN-2
 (1199 14 (:DEFINITION PERMP))
 (842 39 (:REWRITE PERMP-SYMMETRIC))
 (764 39 (:REWRITE CONS-DEL-PERMUTATION-OF-ORIGINAL))
 (652 23 (:DEFINITION DEL))
 (590 47 (:REWRITE UNSUCCESFUL-DEL-PRESERVES-SET))
 (512 239 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (277 277 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (171 159 (:REWRITE DEFAULT-CAR))
 (132 122 (:REWRITE DEFAULT-CDR))
 (127 1 (:REWRITE SUCCESFUL-DEL-PRESERVES-PERMP))
 (97 1 (:REWRITE DEL-COMMUTES))
 (77 5 (:REWRITE DEL-DIFFERENT-ELEMENT-PRESERVES-MEMBER))
 (76 38 (:TYPE-PRESCRIPTION TRUE-LISTP-DEL))
 (39 39 (:REWRITE PERMP-TRANSITIVE))
 (31 2 (:REWRITE DEL-SAME-MEMBER-PRESERVES-PERMP))
 (24 4 (:REWRITE NOT-IN-TEST-FOR-ALL-CDR))
 (18 18 (:REWRITE NOT-IN-TEST-FOR-ALL-SUBSET-APPEND))
 (18 18 (:REWRITE NOT-IN-TEST-FOR-ALL-SUBSET))
 (17 1 (:REWRITE DEL-PRESERVES-PERMP))
 (8 8 (:REWRITE NOT-IN-TEST-FOR-ALL-HOLDS-FOR-MEMBER))
 (8 8 (:REWRITE NOT-IN-TEST-FOR-ALL-HOLDS-FOR-ASSOC))
 (6 6 (:REWRITE CAR-CONS))
 (5 5 (:REWRITE CDR-CONS))
 )
(NOT-IN-APPEND-ALT
 (270 135 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (202 56 (:REWRITE NOT-IN-TEST-FOR-ALL-SUBSET-APPEND))
 (135 135 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (131 4 (:DEFINITION SUBSETP-EQUAL))
 (96 2 (:REWRITE SUBSET-STABLE-UNDER-APPEND))
 (90 15 (:REWRITE NOT-IN-TEST-FOR-ALL-CDR))
 (84 84 (:REWRITE DEFAULT-CAR))
 (74 74 (:REWRITE DEFAULT-CDR))
 (56 56 (:REWRITE NOT-IN-TEST-FOR-ALL-SUBSET))
 (42 24 (:REWRITE NOT-IN-TEST-FOR-ALL-HOLDS-FOR-MEMBER))
 (33 11 (:DEFINITION BINARY-APPEND))
 (24 24 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (24 24 (:REWRITE NOT-IN-TEST-FOR-ALL-HOLDS-FOR-ASSOC))
 (1 1 (:REWRITE SET-IS-SUBSET-OF-APPENDING-ITSELF-ALT))
 (1 1 (:REWRITE SET-IS-SUBSET-OF-APPENDING-ITSELF))
 )
(NOT-IN-EMPTY-LIST-ALWAYS-TRUE
 (154 8 (:REWRITE NOT-IN-TEST-FOR-ALL-SUBSET-APPEND))
 (131 4 (:DEFINITION SUBSETP-EQUAL))
 (116 58 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (96 2 (:REWRITE SUBSET-STABLE-UNDER-APPEND))
 (58 58 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (34 1 (:REWRITE MEMBER-OF-APPEND-IFF-MEMBER-OF-OPERAND))
 (24 24 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (21 3 (:REWRITE NOT-IN-TEST-FOR-ALL-HOLDS-FOR-MEMBER))
 (18 18 (:REWRITE DEFAULT-CAR))
 (16 16 (:REWRITE DEFAULT-CDR))
 (12 2 (:REWRITE NOT-IN-TEST-FOR-ALL-CDR))
 (8 8 (:REWRITE NOT-IN-TEST-FOR-ALL-SUBSET))
 (3 3 (:REWRITE NOT-IN-TEST-FOR-ALL-HOLDS-FOR-ASSOC))
 (3 1 (:DEFINITION BINARY-APPEND))
 (1 1 (:REWRITE SET-IS-SUBSET-OF-APPENDING-ITSELF-ALT))
 (1 1 (:REWRITE SET-IS-SUBSET-OF-APPENDING-ITSELF))
 )
(SUBSET-NOT-IN
 (1058 529 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (529 529 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (216 18 (:REWRITE NOT-IN-TEST-FOR-ALL-CDR))
 (187 41 (:REWRITE NOT-IN-TEST-FOR-ALL-SUBSET-APPEND))
 (107 107 (:REWRITE DEFAULT-CAR))
 (96 2 (:REWRITE SUBSET-STABLE-UNDER-APPEND))
 (87 87 (:REWRITE DEFAULT-CDR))
 (66 41 (:REWRITE NOT-IN-EMPTY-LIST-ALWAYS-TRUE))
 (41 41 (:REWRITE NOT-IN-TEST-FOR-ALL-SUBSET))
 (36 18 (:REWRITE NOT-IN-TEST-FOR-ALL-HOLDS-FOR-MEMBER))
 (34 1 (:REWRITE MEMBER-OF-APPEND-IFF-MEMBER-OF-OPERAND))
 (18 18 (:REWRITE NOT-IN-TEST-FOR-ALL-HOLDS-FOR-ASSOC))
 (3 1 (:DEFINITION BINARY-APPEND))
 (1 1 (:REWRITE SET-IS-SUBSET-OF-APPENDING-ITSELF-ALT))
 (1 1 (:REWRITE SET-IS-SUBSET-OF-APPENDING-ITSELF))
 )
(NO-DUPS-APPEND
 (255 75 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (217 105 (:REWRITE DEFAULT-CDR))
 (198 99 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (182 85 (:REWRITE DEFAULT-CAR))
 (174 174 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (99 99 (:TYPE-PRESCRIPTION CONSP-APPEND . 2))
 (99 99 (:TYPE-PRESCRIPTION CONSP-APPEND . 1))
 (99 99 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (24 3 (:REWRITE NOT-IN-TEST-FOR-ALL-CDR))
 (21 21 (:REWRITE CONSP-APPEND))
 (19 11 (:REWRITE NOT-IN-EMPTY-LIST-ALWAYS-TRUE))
 (11 11 (:REWRITE SUBSET-NOT-IN))
 (11 11 (:REWRITE NOT-IN-TEST-FOR-ALL-SUBSET-APPEND))
 (11 11 (:REWRITE NOT-IN-TEST-FOR-ALL-SUBSET))
 (4 4 (:REWRITE NOT-IN-TEST-FOR-ALL-HOLDS-FOR-MEMBER))
 (4 4 (:REWRITE NOT-IN-TEST-FOR-ALL-HOLDS-FOR-ASSOC))
 )
(SUBSETP-EXPAND
 (43 43 (:REWRITE DEFAULT-CAR))
 (22 22 (:REWRITE DEFAULT-CDR))
 )
(SUBSETP-X-X
 (70 35 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (35 35 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (22 22 (:REWRITE DEFAULT-CAR))
 (19 19 (:REWRITE DEFAULT-CDR))
 )
(SUBSETP-APPEND
 (36 4 (:DEFINITION SUBSETP-EQUAL))
 (12 4 (:DEFINITION MEMBER-EQUAL))
 (9 9 (:REWRITE DEFAULT-CDR))
 (9 9 (:REWRITE DEFAULT-CAR))
 (8 4 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (7 7 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (6 3 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (4 4 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (3 3 (:TYPE-PRESCRIPTION CONSP-APPEND . 2))
 (3 3 (:TYPE-PRESCRIPTION CONSP-APPEND . 1))
 (3 3 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (3 1 (:DEFINITION BINARY-APPEND))
 )
(SUBSETP-TRANS
 (1534 767 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (767 767 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (116 116 (:REWRITE DEFAULT-CAR))
 (89 89 (:REWRITE DEFAULT-CDR))
 )
(SUBSETP-CONS-CDR-PART
 (3 1 (:DEFINITION MEMBER-EQUAL))
 (2 2 (:REWRITE SUBSETP-TRANS))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(SUBSETP-CONS-CAR-PART
 (34 17 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (17 17 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE SUBSETP-TRANS))
 (1 1 (:REWRITE SUBSETP-CONS-CDR-PART))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(TOMISSIVE-TM)
(TOMISSIVE-TM-MAP-MAPPABLE)
(TOMISSIVES)
(TOMISSIVE-TM-MAP-APPEND)
(TOMISSIVE-TM-MEMBER-OF-MAP)
(TOMISSIVE-TM-MEMBER-OF-MAP-EQUAL)
(TOMISSIVE-TM-MAP-MEMBER-OF-DEL)
(TOMISSIVE-TM-PERMP-IMPLIES-PERMP-DO-MAP-1)
(TOMISSIVE-TM-MAP-LEN)
(TOMISSIVE-TM-MAP-TRUE-LISTP)
(TOMISSIVE-TM-MAP-SUBSETP-IMPLIES-MEMBER-V)
(TOMISSIVE-TM-SUBSETP-IMPLIES-SUBSET-OF-MAP)
(M-IDS-TOMISSIVES
 (21 20 (:REWRITE DEFAULT-CAR))
 (19 18 (:REWRITE DEFAULT-CDR))
 )
(FWD-MISSIVESP
 (15 1 (:DEFINITION SUBSETP-EQUAL))
 (14 1 (:DEFINITION VALIDFIELDS-M))
 (12 1 (:DEFINITION NO-DUPLICATESP-EQUAL))
 (9 9 (:REWRITE DEFAULT-CDR))
 (8 2 (:DEFINITION MEMBER-EQUAL))
 (7 7 (:REWRITE DEFAULT-CAR))
 (6 1 (:REWRITE M-P-FOR-ALL-CDR))
 (4 4 (:REWRITE SUBSETP-CONS-CAR-PART))
 (3 3 (:REWRITE M-P-FOR-ALL-SUBSET-APPEND))
 (3 3 (:REWRITE M-P-FOR-ALL-SUBSET))
 (3 2 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (3 1 (:DEFINITION V-IDS))
 (3 1 (:DEFINITION M-ORGS))
 (2 2 (:TYPE-PRESCRIPTION V-ID-MAP-TRUE-LISTP))
 (2 2 (:REWRITE SUBSETP-TRANS))
 (2 2 (:REWRITE SUBSETP-CONS-CDR-PART))
 (2 1 (:DEFINITION TRUE-LISTP))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (1 1 (:TYPE-PRESCRIPTION M-P))
 (1 1 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (1 1 (:REWRITE M-P-FOR-ALL-HOLDS-FOR-MEMBER))
 (1 1 (:REWRITE M-P-FOR-ALL-HOLDS-FOR-ASSOC))
 )
(TOMISSIVES-TRUELISTP)
(TO-MISSIVES-MISSIVESP
 (2937 75 (:REWRITE NATP-FOR-ALL-SUBSET-APPEND))
 (2427 25 (:DEFINITION A-NATP))
 (2199 75 (:REWRITE LEN=-FOR-ALL-SUBSET-APPEND))
 (2028 25 (:DEFINITION A-LEN=))
 (1726 32 (:REWRITE VALIDFIELDS-TM-TEST-FOR-ALL-CDR))
 (1412 1391 (:REWRITE DEFAULT-CDR))
 (1329 1310 (:REWRITE DEFAULT-CAR))
 (1080 25 (:REWRITE NATP-FOR-ALL-CDR))
 (1018 1018 (:TYPE-PRESCRIPTION CADRS))
 (989 37 (:REWRITE MEMBER-OF-APPEND-IFF-MEMBER-OF-OPERAND))
 (858 25 (:REWRITE LEN=-FOR-ALL-CDR))
 (789 25 (:DEFINITION PER-RESOURCE-NO-DUPLICATE-FLITS))
 (675 675 (:REWRITE SUBSETP-CONS-CAR-PART))
 (526 526 (:REWRITE SUBSETP-CONS-CDR-PART))
 (505 97 (:REWRITE NATP-FOR-ALL-HOLDS-FOR-MEMBER))
 (300 50 (:DEFINITION CADRS))
 (250 50 (:DEFINITION LEN))
 (193 25 (:DEFINITION LEN=))
 (154 38 (:DEFINITION BINARY-APPEND))
 (150 25 (:DEFINITION FILTER-CAR=-ALT))
 (146 146 (:REWRITE DEFAULT-<-2))
 (146 146 (:REWRITE DEFAULT-<-1))
 (100 50 (:REWRITE DEFAULT-+-2))
 (100 25 (:DEFINITION STRIP-CARS))
 (99 6 (:REWRITE DEFS-M-P-INCLUDES-WEAK-M-P))
 (97 97 (:REWRITE NATP-FOR-ALL-HOLDS-FOR-ASSOC))
 (85 25 (:REWRITE LEN=-FOR-ALL-HOLDS-FOR-MEMBER))
 (75 75 (:REWRITE NATP-FOR-ALL-SUBSET))
 (75 75 (:REWRITE LEN=-FOR-ALL-SUBSET))
 (75 25 (:REWRITE DEFS-TM-P-INCLUDES-WEAK-TM-P))
 (67 67 (:REWRITE VALIDFIELDS-TM-TEST-FOR-ALL-SUBSET-APPEND))
 (67 67 (:REWRITE VALIDFIELDS-TM-TEST-FOR-ALL-SUBSET))
 (53 53 (:TYPE-PRESCRIPTION STRIP-CARS))
 (50 50 (:TYPE-PRESCRIPTION TM-P))
 (50 50 (:TYPE-PRESCRIPTION FILTER-CAR=-TEST-FILTER-TRUE-LISTP))
 (50 50 (:REWRITE DEFAULT-+-1))
 (50 25 (:DEFINITION FILTER-CAR=-TEST))
 (28 10 (:REWRITE M-P-FOR-ALL-HOLDS-FOR-MEMBER))
 (25 25 (:REWRITE LEN=-FOR-ALL-HOLDS-FOR-ASSOC))
 (24 4 (:REWRITE M-P-FOR-ALL-CDR))
 (19 19 (:REWRITE VALIDFIELDS-TM-TEST-FOR-ALL-HOLDS-FOR-MEMBER))
 (19 19 (:REWRITE VALIDFIELDS-TM-TEST-FOR-ALL-HOLDS-FOR-ASSOC))
 (14 14 (:TYPE-PRESCRIPTION M-P))
 (13 13 (:REWRITE M-P-FOR-ALL-SUBSET))
 (12 12 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (10 10 (:REWRITE M-P-FOR-ALL-HOLDS-FOR-ASSOC))
 (8 2 (:REWRITE SET-IS-SUBSET-OF-APPENDING-ITSELF-ALT))
 (5 5 (:REWRITE TOMISSIVE-TM-MAP-SUBSETP-IMPLIES-MEMBER-V))
 (4 4 (:REWRITE V-ID-MAP-SUBSETP-IMPLIES-MEMBER-V))
 )
(REWRITE-MISSIVESP-APPEND
 (721 13 (:REWRITE M-P-FOR-ALL-SUBSET-APPEND))
 (654 28 (:DEFINITION SUBSETP-EQUAL))
 (548 4 (:DEFINITION VALIDFIELDS-M))
 (486 12 (:REWRITE SUBSET-STABLE-UNDER-APPEND))
 (268 42 (:DEFINITION MEMBER-EQUAL))
 (260 4 (:REWRITE M-P-FOR-ALL-CDR))
 (180 172 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (120 6 (:REWRITE MEMBER-OF-APPEND-IFF-MEMBER-OF-OPERAND))
 (106 106 (:REWRITE DEFAULT-CDR))
 (99 99 (:REWRITE DEFAULT-CAR))
 (90 90 (:REWRITE SUBSETP-CONS-CAR-PART))
 (75 75 (:REWRITE SUBSETP-TRANS))
 (75 75 (:REWRITE SUBSETP-CONS-CDR-PART))
 (74 2 (:DEFINITION NOT-IN))
 (48 4 (:DEFINITION NO-DUPLICATESP-EQUAL))
 (38 38 (:TYPE-PRESCRIPTION V-ID-MAP-TRUE-LISTP))
 (31 9 (:DEFINITION BINARY-APPEND))
 (26 6 (:REWRITE NOT-IN-EMPTY-LIST-ALWAYS-TRUE))
 (24 4 (:REWRITE M-P-FOR-ALL-HOLDS-FOR-MEMBER))
 (22 2 (:DEFINITION NOT-IN-TEST))
 (18 6 (:DEFINITION V-IDS))
 (16 4 (:DEFINITION ENDP))
 (16 2 (:REWRITE NOT-IN-TEST-FOR-ALL-CDR))
 (13 13 (:REWRITE M-P-FOR-ALL-SUBSET))
 (12 4 (:DEFINITION M-ORGS))
 (10 10 (:TYPE-PRESCRIPTION M-ORG-MAP-TRUE-LISTP))
 (6 6 (:REWRITE SUBSET-NOT-IN))
 (6 6 (:REWRITE NOT-IN-TEST-FOR-ALL-SUBSET-APPEND))
 (6 6 (:REWRITE NOT-IN-TEST-FOR-ALL-SUBSET))
 (6 3 (:DEFINITION TRUE-LISTP))
 (4 4 (:TYPE-PRESCRIPTION M-P))
 (4 4 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (4 4 (:REWRITE M-P-FOR-ALL-HOLDS-FOR-ASSOC))
 (2 2 (:REWRITE V-ID-MAP-SUBSETP-IMPLIES-MEMBER-V))
 (2 2 (:REWRITE NOT-IN-TEST-FOR-ALL-HOLDS-FOR-MEMBER))
 (2 2 (:REWRITE NOT-IN-TEST-FOR-ALL-HOLDS-FOR-ASSOC))
 (2 1 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (1 1 (:TYPE-PRESCRIPTION CONSP-APPEND . 2))
 (1 1 (:TYPE-PRESCRIPTION CONSP-APPEND . 1))
 (1 1 (:TYPE-PRESCRIPTION BINARY-APPEND))
 )
(MISSIVESY-MISSIVES-CDRY
 (79 14 (:DEFINITION MEMBER-EQUAL))
 (59 56 (:REWRITE DEFAULT-CDR))
 (49 47 (:REWRITE DEFAULT-CAR))
 (29 29 (:REWRITE SUBSETP-CONS-CAR-PART))
 (28 8 (:REWRITE M-P-FOR-ALL-HOLDS-FOR-MEMBER))
 (20 1 (:REWRITE MEMBER-OF-APPEND-IFF-MEMBER-OF-OPERAND))
 (17 17 (:REWRITE M-P-FOR-ALL-SUBSET))
 (11 1 (:REWRITE V-ID-MEMBER-OF-MAP))
 (8 8 (:REWRITE M-P-FOR-ALL-HOLDS-FOR-ASSOC))
 (6 2 (:DEFINITION BINARY-APPEND))
 (2 2 (:REWRITE SET-IS-SUBSET-OF-APPENDING-ITSELF-ALT))
 (1 1 (:REWRITE V-ID-MEMBER-OF-MAP-EQUAL))
 (1 1 (:REWRITE V-ID-MAP-SUBSETP-IMPLIES-MEMBER-V))
 )
(TOTMISSIVE-V)
(TOTMISSIVE-V-MAP-MAPPABLE)
(TOTMISSIVES)
(TOTMISSIVE-V-MAP-APPEND)
(TOTMISSIVE-V-MEMBER-OF-MAP)
(TOTMISSIVE-V-MEMBER-OF-MAP-EQUAL)
(TOTMISSIVE-V-MAP-MEMBER-OF-DEL)
(TOTMISSIVE-V-PERMP-IMPLIES-PERMP-DO-MAP-1)
(TOTMISSIVE-V-MAP-LEN)
(TOTMISSIVE-V-MAP-TRUE-LISTP)
(TOTMISSIVE-V-MAP-SUBSETP-IMPLIES-MEMBER-V)
(TOTMISSIVE-V-SUBSETP-IMPLIES-SUBSET-OF-MAP)
(TOMISSIVE-V)
(EQUAL-LOCS)
(TM-IDS-TOMISSIVES-V-IDS
 (21 20 (:REWRITE DEFAULT-CAR))
 (19 18 (:REWRITE DEFAULT-CDR))
 )
(TMISSIVESP-TOMISSIVES-BIS
 (2028 24 (:REWRITE VALIDFIELDS-TRLST-TEST-FOR-ALL-CDR))
 (1737 23 (:DEFINITION A-NATP))
 (1561 1547 (:REWRITE DEFAULT-CDR))
 (1494 23 (:DEFINITION A-LEN=))
 (1177 1165 (:REWRITE DEFAULT-CAR))
 (897 897 (:TYPE-PRESCRIPTION CADRS))
 (779 65 (:REWRITE NATP-FOR-ALL-HOLDS-FOR-MEMBER))
 (758 23 (:REWRITE NATP-FOR-ALL-CDR))
 (671 25 (:REWRITE MEMBER-OF-APPEND-IFF-MEMBER-OF-OPERAND))
 (619 619 (:REWRITE SUBSETP-CONS-CAR-PART))
 (610 23 (:REWRITE LEN=-FOR-ALL-CDR))
 (384 384 (:REWRITE SUBSETP-CONS-CDR-PART))
 (288 48 (:DEFINITION CADRS))
 (179 23 (:DEFINITION LEN=))
 (172 43 (:DEFINITION STRIP-CARS))
 (144 24 (:DEFINITION FILTER-CAR=-ALT))
 (114 28 (:DEFINITION BINARY-APPEND))
 (97 97 (:REWRITE DEFAULT-<-2))
 (97 97 (:REWRITE DEFAULT-<-1))
 (94 47 (:REWRITE DEFAULT-+-2))
 (90 90 (:TYPE-PRESCRIPTION STRIP-CARS))
 (69 69 (:REWRITE NATP-FOR-ALL-SUBSET))
 (69 69 (:REWRITE LEN=-FOR-ALL-SUBSET))
 (65 65 (:REWRITE NATP-FOR-ALL-HOLDS-FOR-ASSOC))
 (63 23 (:REWRITE LEN=-FOR-ALL-HOLDS-FOR-MEMBER))
 (57 19 (:REWRITE DEFS-V-P-INCLUDES-WEAK-V-P))
 (51 51 (:REWRITE VALIDFIELDS-TRLST-TEST-FOR-ALL-SUBSET-APPEND))
 (51 51 (:REWRITE VALIDFIELDS-TRLST-TEST-FOR-ALL-SUBSET))
 (48 48 (:TYPE-PRESCRIPTION FILTER-CAR=-TEST-FILTER-TRUE-LISTP))
 (48 24 (:DEFINITION FILTER-CAR=-TEST))
 (47 47 (:REWRITE DEFAULT-+-1))
 (38 38 (:TYPE-PRESCRIPTION V-P))
 (24 4 (:REWRITE VALIDFIELDS-TM-TEST-FOR-ALL-CDR))
 (23 23 (:REWRITE LEN=-FOR-ALL-HOLDS-FOR-ASSOC))
 (23 5 (:REWRITE VALIDFIELDS-TM-TEST-FOR-ALL-HOLDS-FOR-MEMBER))
 (15 15 (:REWRITE VALIDFIELDS-TRLST-TEST-FOR-ALL-HOLDS-FOR-MEMBER))
 (15 15 (:REWRITE VALIDFIELDS-TRLST-TEST-FOR-ALL-HOLDS-FOR-ASSOC))
 (14 14 (:REWRITE VALIDFIELDS-TM-TEST-FOR-ALL-SUBSET))
 (13 4 (:REWRITE SET-IS-SUBSET-OF-APPENDING-ITSELF-ALT))
 (12 12 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (5 5 (:REWRITE VALIDFIELDS-TM-TEST-FOR-ALL-HOLDS-FOR-ASSOC))
 (5 5 (:REWRITE TOTMISSIVE-V-MAP-SUBSETP-IMPLIES-MEMBER-V))
 (4 4 (:REWRITE V-ID-MAP-SUBSETP-IMPLIES-MEMBER-V))
 )
(FWD-TMISSIVESP
 (155 1 (:DEFINITION VALIDFIELDS-TM))
 (136 1 (:DEFINITION VALIDFIELDS-TM-TEST))
 (112 1 (:DEFINITION VALIDFIELD-LOC))
 (45 3 (:DEFINITION SUBSETP-EQUAL))
 (30 1 (:DEFINITION PER-RESOURCE-NO-DUPLICATE-FLITS))
 (29 29 (:REWRITE DEFAULT-CDR))
 (29 29 (:REWRITE DEFAULT-CAR))
 (24 2 (:DEFINITION NO-DUPLICATESP-EQUAL))
 (21 1 (:DEFINITION A-LEN=))
 (20 5 (:DEFINITION MEMBER-EQUAL))
 (18 1 (:DEFINITION A-NATP))
 (12 4 (:DEFINITION NATP))
 (12 2 (:DEFINITION CADRS))
 (10 10 (:REWRITE SUBSETP-CONS-CAR-PART))
 (10 2 (:DEFINITION LEN))
 (8 5 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (7 1 (:DEFINITION LEN=))
 (6 6 (:TYPE-PRESCRIPTION LEN))
 (6 6 (:REWRITE SUBSETP-TRANS))
 (6 6 (:REWRITE SUBSETP-CONS-CDR-PART))
 (6 1 (:REWRITE VALIDFIELDS-TM-TEST-FOR-ALL-CDR))
 (6 1 (:REWRITE NATP-FOR-ALL-CDR))
 (6 1 (:REWRITE LEN=-FOR-ALL-CDR))
 (6 1 (:DEFINITION FILTER-CAR=-ALT))
 (5 5 (:TYPE-PRESCRIPTION A-NATP))
 (5 5 (:TYPE-PRESCRIPTION A-LEN=))
 (5 5 (:REWRITE DEFAULT-<-2))
 (5 5 (:REWRITE DEFAULT-<-1))
 (4 4 (:TYPE-PRESCRIPTION CADRS))
 (4 4 (:REWRITE NATP-FOR-ALL-HOLDS-FOR-MEMBER))
 (4 4 (:REWRITE NATP-FOR-ALL-HOLDS-FOR-ASSOC))
 (4 2 (:REWRITE DEFAULT-+-2))
 (4 2 (:DEFINITION TRUE-LISTP))
 (4 1 (:DEFINITION STRIP-CARS))
 (3 3 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (3 3 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (3 3 (:REWRITE VALIDFIELDS-TM-TEST-FOR-ALL-SUBSET-APPEND))
 (3 3 (:REWRITE VALIDFIELDS-TM-TEST-FOR-ALL-SUBSET))
 (3 3 (:REWRITE NATP-FOR-ALL-SUBSET-APPEND))
 (3 3 (:REWRITE NATP-FOR-ALL-SUBSET))
 (3 3 (:REWRITE LEN=-FOR-ALL-SUBSET-APPEND))
 (3 3 (:REWRITE LEN=-FOR-ALL-SUBSET))
 (3 1 (:REWRITE DEFS-TM-P-INCLUDES-WEAK-TM-P))
 (3 1 (:DEFINITION V-IDS))
 (3 1 (:DEFINITION TM-ORGS))
 (3 1 (:DEFINITION TM-CURS))
 (2 2 (:TYPE-PRESCRIPTION WEAK-TM-P))
 (2 2 (:TYPE-PRESCRIPTION V-ID-MAP-TRUE-LISTP))
 (2 2 (:TYPE-PRESCRIPTION TM-P))
 (2 2 (:TYPE-PRESCRIPTION STRIP-CARS))
 (2 2 (:TYPE-PRESCRIPTION PER-RESOURCE-NO-DUPLICATE-FLITS))
 (2 2 (:TYPE-PRESCRIPTION FILTER-CAR=-TEST-FILTER-TRUE-LISTP))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 1 (:DEFINITION FILTER-CAR=-TEST))
 (1 1 (:REWRITE VALIDFIELDS-TM-TEST-FOR-ALL-HOLDS-FOR-MEMBER))
 (1 1 (:REWRITE VALIDFIELDS-TM-TEST-FOR-ALL-HOLDS-FOR-ASSOC))
 (1 1 (:REWRITE LEN=-FOR-ALL-HOLDS-FOR-MEMBER))
 (1 1 (:REWRITE LEN=-FOR-ALL-HOLDS-FOR-ASSOC))
 )
(TMISSIVESY-TMISSIVES-CDRY
 (1206 138 (:DEFINITION MEMBER-EQUAL))
 (1117 7 (:DEFINITION A-NATP))
 (903 7 (:DEFINITION A-LEN=))
 (507 507 (:TYPE-PRESCRIPTION CADRS))
 (507 7 (:REWRITE NATP-FOR-ALL-CDR))
 (497 19 (:REWRITE MEMBER-OF-APPEND-IFF-MEMBER-OF-OPERAND))
 (459 456 (:REWRITE DEFAULT-CAR))
 (415 411 (:REWRITE DEFAULT-CDR))
 (396 7 (:REWRITE LEN=-FOR-ALL-CDR))
 (295 295 (:REWRITE SUBSETP-CONS-CAR-PART))
 (234 20 (:REWRITE VALIDFIELDS-TM-TEST-FOR-ALL-SUBSET))
 (226 22 (:REWRITE NATP-FOR-ALL-HOLDS-FOR-MEMBER))
 (108 18 (:DEFINITION CADRS))
 (94 24 (:DEFINITION BINARY-APPEND))
 (61 7 (:DEFINITION LEN=))
 (54 9 (:DEFINITION FILTER-CAR=-ALT))
 (37 7 (:REWRITE LEN=-FOR-ALL-HOLDS-FOR-MEMBER))
 (36 9 (:DEFINITION STRIP-CARS))
 (35 35 (:REWRITE DEFAULT-<-2))
 (35 35 (:REWRITE DEFAULT-<-1))
 (32 16 (:REWRITE DEFAULT-+-2))
 (27 9 (:REWRITE DEFS-TM-P-INCLUDES-WEAK-TM-P))
 (22 22 (:REWRITE NATP-FOR-ALL-HOLDS-FOR-ASSOC))
 (21 21 (:REWRITE NATP-FOR-ALL-SUBSET))
 (21 21 (:REWRITE LEN=-FOR-ALL-SUBSET))
 (18 18 (:TYPE-PRESCRIPTION TM-P))
 (18 18 (:TYPE-PRESCRIPTION FILTER-CAR=-TEST-FILTER-TRUE-LISTP))
 (18 9 (:DEFINITION FILTER-CAR=-TEST))
 (17 7 (:REWRITE VALIDFIELDS-TM-TEST-FOR-ALL-HOLDS-FOR-MEMBER))
 (16 16 (:TYPE-PRESCRIPTION STRIP-CARS))
 (16 16 (:REWRITE DEFAULT-+-1))
 (12 6 (:REWRITE SET-IS-SUBSET-OF-APPENDING-ITSELF-ALT))
 (11 1 (:REWRITE V-ID-MEMBER-OF-MAP))
 (9 9 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (7 7 (:REWRITE VALIDFIELDS-TM-TEST-FOR-ALL-HOLDS-FOR-ASSOC))
 (7 7 (:REWRITE LEN=-FOR-ALL-HOLDS-FOR-ASSOC))
 (1 1 (:REWRITE V-ID-MEMBER-OF-MAP-EQUAL))
 (1 1 (:REWRITE V-ID-MAP-SUBSETP-IMPLIES-MEMBER-V))
 )
(REWRITE-NODUPS-TM-IDS-APPEND
 (74 2 (:DEFINITION NOT-IN))
 (48 4 (:DEFINITION NO-DUPLICATESP-EQUAL))
 (38 38 (:TYPE-PRESCRIPTION V-ID-MAP-TRUE-LISTP))
 (28 6 (:DEFINITION MEMBER-EQUAL))
 (26 6 (:REWRITE NOT-IN-EMPTY-LIST-ALWAYS-TRUE))
 (23 23 (:REWRITE DEFAULT-CDR))
 (22 2 (:DEFINITION NOT-IN-TEST))
 (19 19 (:REWRITE DEFAULT-CAR))
 (18 6 (:DEFINITION V-IDS))
 (16 4 (:DEFINITION ENDP))
 (16 2 (:REWRITE NOT-IN-TEST-FOR-ALL-CDR))
 (12 12 (:REWRITE SUBSETP-CONS-CAR-PART))
 (12 8 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (6 6 (:REWRITE SUBSET-NOT-IN))
 (6 6 (:REWRITE NOT-IN-TEST-FOR-ALL-SUBSET-APPEND))
 (6 6 (:REWRITE NOT-IN-TEST-FOR-ALL-SUBSET))
 (5 1 (:DEFINITION BINARY-APPEND))
 (2 2 (:REWRITE V-ID-MAP-SUBSETP-IMPLIES-MEMBER-V))
 (2 2 (:REWRITE NOT-IN-TEST-FOR-ALL-HOLDS-FOR-MEMBER))
 (2 2 (:REWRITE NOT-IN-TEST-FOR-ALL-HOLDS-FOR-ASSOC))
 )
(REWRITE-VALIDFIELDS-TM-APPEND
 (1332 4 (:DEFINITION VALIDFIELDS-TM))
 (1021 13 (:REWRITE VALIDFIELDS-TM-TEST-FOR-ALL-SUBSET-APPEND))
 (954 28 (:DEFINITION SUBSETP-EQUAL))
 (666 12 (:REWRITE SUBSET-STABLE-UNDER-APPEND))
 (544 4 (:DEFINITION VALIDFIELDS-TM-TEST))
 (448 40 (:DEFINITION MEMBER-EQUAL))
 (448 4 (:DEFINITION VALIDFIELD-LOC))
 (360 4 (:REWRITE VALIDFIELDS-TM-TEST-FOR-ALL-CDR))
 (332 168 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (228 6 (:REWRITE MEMBER-OF-APPEND-IFF-MEMBER-OF-OPERAND))
 (170 170 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (164 164 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (164 164 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (143 143 (:REWRITE DEFAULT-CAR))
 (135 135 (:REWRITE DEFAULT-CDR))
 (120 4 (:DEFINITION PER-RESOURCE-NO-DUPLICATE-FLITS))
 (86 86 (:REWRITE SUBSETP-CONS-CAR-PART))
 (84 4 (:DEFINITION A-LEN=))
 (74 74 (:REWRITE SUBSETP-TRANS))
 (74 74 (:REWRITE SUBSETP-CONS-CDR-PART))
 (72 4 (:DEFINITION A-NATP))
 (48 16 (:DEFINITION NATP))
 (48 8 (:DEFINITION CADRS))
 (48 4 (:DEFINITION NO-DUPLICATESP-EQUAL))
 (44 4 (:REWRITE VALIDFIELDS-TM-TEST-FOR-ALL-HOLDS-FOR-MEMBER))
 (40 8 (:DEFINITION LEN))
 (28 4 (:DEFINITION LEN=))
 (24 24 (:TYPE-PRESCRIPTION LEN))
 (24 4 (:REWRITE NATP-FOR-ALL-CDR))
 (24 4 (:REWRITE LEN=-FOR-ALL-CDR))
 (24 4 (:DEFINITION FILTER-CAR=-ALT))
 (21 7 (:DEFINITION BINARY-APPEND))
 (20 20 (:TYPE-PRESCRIPTION A-NATP))
 (20 20 (:TYPE-PRESCRIPTION A-LEN=))
 (20 20 (:REWRITE DEFAULT-<-2))
 (20 20 (:REWRITE DEFAULT-<-1))
 (16 16 (:TYPE-PRESCRIPTION CADRS))
 (16 16 (:REWRITE NATP-FOR-ALL-HOLDS-FOR-MEMBER))
 (16 16 (:REWRITE NATP-FOR-ALL-HOLDS-FOR-ASSOC))
 (16 8 (:REWRITE DEFAULT-+-2))
 (16 4 (:DEFINITION STRIP-CARS))
 (13 13 (:REWRITE VALIDFIELDS-TM-TEST-FOR-ALL-SUBSET))
 (12 12 (:REWRITE NATP-FOR-ALL-SUBSET-APPEND))
 (12 12 (:REWRITE NATP-FOR-ALL-SUBSET))
 (12 12 (:REWRITE LEN=-FOR-ALL-SUBSET-APPEND))
 (12 12 (:REWRITE LEN=-FOR-ALL-SUBSET))
 (12 4 (:REWRITE DEFS-TM-P-INCLUDES-WEAK-TM-P))
 (8 8 (:TYPE-PRESCRIPTION WEAK-TM-P))
 (8 8 (:TYPE-PRESCRIPTION TM-P))
 (8 8 (:TYPE-PRESCRIPTION STRIP-CARS))
 (8 8 (:TYPE-PRESCRIPTION PER-RESOURCE-NO-DUPLICATE-FLITS))
 (8 8 (:TYPE-PRESCRIPTION FILTER-CAR=-TEST-FILTER-TRUE-LISTP))
 (8 8 (:REWRITE DEFAULT-+-1))
 (8 4 (:DEFINITION TRUE-LISTP))
 (8 4 (:DEFINITION FILTER-CAR=-TEST))
 (4 4 (:TYPE-PRESCRIPTION NO-DUPLICATESP-EQUAL))
 (4 4 (:REWRITE VALIDFIELDS-TM-TEST-FOR-ALL-HOLDS-FOR-ASSOC))
 (4 4 (:REWRITE LEN=-FOR-ALL-HOLDS-FOR-MEMBER))
 (4 4 (:REWRITE LEN=-FOR-ALL-HOLDS-FOR-ASSOC))
 )
(REWRITE-TMISSIVESP-APPEND
 (1112 4 (:DEFINITION VALIDFIELDS-TM))
 (774 36 (:DEFINITION SUBSETP-EQUAL))
 (720 12 (:REWRITE VALIDFIELDS-TM-TEST-FOR-ALL-SUBSET-APPEND))
 (544 4 (:DEFINITION VALIDFIELDS-TM-TEST))
 (486 12 (:REWRITE SUBSET-STABLE-UNDER-APPEND))
 (448 4 (:DEFINITION VALIDFIELD-LOC))
 (316 54 (:DEFINITION MEMBER-EQUAL))
 (260 4 (:REWRITE VALIDFIELDS-TM-TEST-FOR-ALL-CDR))
 (200 184 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (188 188 (:REWRITE DEFAULT-CAR))
 (187 187 (:REWRITE DEFAULT-CDR))
 (120 6 (:REWRITE MEMBER-OF-APPEND-IFF-MEMBER-OF-OPERAND))
 (120 4 (:DEFINITION PER-RESOURCE-NO-DUPLICATE-FLITS))
 (114 114 (:REWRITE SUBSETP-CONS-CAR-PART))
 (96 8 (:DEFINITION NO-DUPLICATESP-EQUAL))
 (92 92 (:REWRITE SUBSETP-TRANS))
 (92 92 (:REWRITE SUBSETP-CONS-CDR-PART))
 (84 4 (:DEFINITION A-LEN=))
 (74 2 (:DEFINITION NOT-IN))
 (72 4 (:DEFINITION A-NATP))
 (48 16 (:DEFINITION NATP))
 (48 8 (:DEFINITION CADRS))
 (40 8 (:DEFINITION LEN))
 (38 38 (:TYPE-PRESCRIPTION V-ID-MAP-TRUE-LISTP))
 (36 10 (:DEFINITION BINARY-APPEND))
 (28 4 (:DEFINITION LEN=))
 (26 6 (:REWRITE NOT-IN-EMPTY-LIST-ALWAYS-TRUE))
 (24 24 (:TYPE-PRESCRIPTION LEN))
 (24 4 (:REWRITE VALIDFIELDS-TM-TEST-FOR-ALL-HOLDS-FOR-MEMBER))
 (24 4 (:REWRITE NATP-FOR-ALL-CDR))
 (24 4 (:REWRITE LEN=-FOR-ALL-CDR))
 (24 4 (:DEFINITION FILTER-CAR=-ALT))
 (22 2 (:DEFINITION NOT-IN-TEST))
 (20 20 (:TYPE-PRESCRIPTION A-NATP))
 (20 20 (:TYPE-PRESCRIPTION A-LEN=))
 (20 20 (:REWRITE DEFAULT-<-2))
 (20 20 (:REWRITE DEFAULT-<-1))
 (18 6 (:DEFINITION V-IDS))
 (16 16 (:TYPE-PRESCRIPTION CADRS))
 (16 16 (:REWRITE NATP-FOR-ALL-HOLDS-FOR-MEMBER))
 (16 16 (:REWRITE NATP-FOR-ALL-HOLDS-FOR-ASSOC))
 (16 8 (:REWRITE DEFAULT-+-2))
 (16 4 (:DEFINITION STRIP-CARS))
 (16 4 (:DEFINITION ENDP))
 (16 2 (:REWRITE NOT-IN-TEST-FOR-ALL-CDR))
 (14 7 (:DEFINITION TRUE-LISTP))
 (12 12 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (12 12 (:REWRITE VALIDFIELDS-TM-TEST-FOR-ALL-SUBSET))
 (12 12 (:REWRITE NATP-FOR-ALL-SUBSET-APPEND))
 (12 12 (:REWRITE NATP-FOR-ALL-SUBSET))
 (12 12 (:REWRITE LEN=-FOR-ALL-SUBSET-APPEND))
 (12 12 (:REWRITE LEN=-FOR-ALL-SUBSET))
 (12 4 (:REWRITE DEFS-TM-P-INCLUDES-WEAK-TM-P))
 (12 4 (:DEFINITION TM-ORGS))
 (12 4 (:DEFINITION TM-CURS))
 (10 10 (:TYPE-PRESCRIPTION TM-ORG-MAP-TRUE-LISTP))
 (10 10 (:TYPE-PRESCRIPTION TM-CUR-MAP-TRUE-LISTP))
 (8 8 (:TYPE-PRESCRIPTION WEAK-TM-P))
 (8 8 (:TYPE-PRESCRIPTION TM-P))
 (8 8 (:TYPE-PRESCRIPTION STRIP-CARS))
 (8 8 (:TYPE-PRESCRIPTION PER-RESOURCE-NO-DUPLICATE-FLITS))
 (8 8 (:TYPE-PRESCRIPTION FILTER-CAR=-TEST-FILTER-TRUE-LISTP))
 (8 8 (:REWRITE DEFAULT-+-1))
 (8 4 (:DEFINITION FILTER-CAR=-TEST))
 (6 6 (:REWRITE SUBSET-NOT-IN))
 (6 6 (:REWRITE NOT-IN-TEST-FOR-ALL-SUBSET-APPEND))
 (6 6 (:REWRITE NOT-IN-TEST-FOR-ALL-SUBSET))
 (4 4 (:REWRITE VALIDFIELDS-TM-TEST-FOR-ALL-HOLDS-FOR-ASSOC))
 (4 4 (:REWRITE LEN=-FOR-ALL-HOLDS-FOR-MEMBER))
 (4 4 (:REWRITE LEN=-FOR-ALL-HOLDS-FOR-ASSOC))
 (2 2 (:REWRITE V-ID-MAP-SUBSETP-IMPLIES-MEMBER-V))
 (2 2 (:REWRITE NOT-IN-TEST-FOR-ALL-HOLDS-FOR-MEMBER))
 (2 2 (:REWRITE NOT-IN-TEST-FOR-ALL-HOLDS-FOR-ASSOC))
 (2 1 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (1 1 (:TYPE-PRESCRIPTION CONSP-APPEND . 2))
 (1 1 (:TYPE-PRESCRIPTION CONSP-APPEND . 1))
 (1 1 (:TYPE-PRESCRIPTION BINARY-APPEND))
 )
(REWRITE-TRLSTP-APPEND
 (1460 4 (:DEFINITION VALIDFIELDS-TRLST))
 (864 4 (:DEFINITION VALIDFIELDS-TRLST-TEST))
 (721 13 (:REWRITE VALIDFIELDS-TRLST-TEST-FOR-ALL-SUBSET-APPEND))
 (714 32 (:DEFINITION SUBSETP-EQUAL))
 (588 4 (:DEFINITION VALIDFIELD-TRAVELP))
 (486 12 (:REWRITE SUBSET-STABLE-UNDER-APPEND))
 (448 4 (:DEFINITION VALIDFIELD-LOC))
 (428 66 (:DEFINITION MEMBER-EQUAL))
 (296 240 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (260 4 (:REWRITE VALIDFIELDS-TRLST-TEST-FOR-ALL-CDR))
 (194 194 (:REWRITE DEFAULT-CAR))
 (193 193 (:REWRITE DEFAULT-CDR))
 (186 186 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (148 12 (:REWRITE NATP-FOR-ALL-HOLDS-FOR-MEMBER))
 (138 138 (:REWRITE SUBSETP-CONS-CAR-PART))
 (120 6 (:REWRITE MEMBER-OF-APPEND-IFF-MEMBER-OF-OPERAND))
 (120 4 (:DEFINITION PER-RESOURCE-NO-DUPLICATE-FLITS))
 (96 8 (:DEFINITION NO-DUPLICATESP-EQUAL))
 (84 4 (:DEFINITION A-LEN=))
 (82 82 (:REWRITE SUBSETP-TRANS))
 (82 82 (:REWRITE SUBSETP-CONS-CDR-PART))
 (74 2 (:DEFINITION NOT-IN))
 (72 72 (:TYPE-PRESCRIPTION CADRS))
 (72 4 (:DEFINITION A-NATP))
 (48 8 (:DEFINITION CADRS))
 (40 8 (:DEFINITION LEN))
 (38 38 (:TYPE-PRESCRIPTION V-ID-MAP-TRUE-LISTP))
 (36 12 (:DEFINITION NATP))
 (32 8 (:DEFINITION STRIP-CARS))
 (28 28 (:TYPE-PRESCRIPTION LEN))
 (28 28 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (28 4 (:DEFINITION LEN=))
 (26 8 (:DEFINITION BINARY-APPEND))
 (26 6 (:REWRITE NOT-IN-EMPTY-LIST-ALWAYS-TRUE))
 (24 24 (:TYPE-PRESCRIPTION A-NATP))
 (24 24 (:TYPE-PRESCRIPTION A-LEN=))
 (24 4 (:REWRITE VALIDFIELDS-TRLST-TEST-FOR-ALL-HOLDS-FOR-MEMBER))
 (24 4 (:REWRITE NATP-FOR-ALL-CDR))
 (24 4 (:REWRITE LEN=-FOR-ALL-CDR))
 (24 4 (:DEFINITION FILTER-CAR=-ALT))
 (22 11 (:DEFINITION TRUE-LISTP))
 (22 2 (:DEFINITION NOT-IN-TEST))
 (18 6 (:DEFINITION V-IDS))
 (16 16 (:TYPE-PRESCRIPTION STRIP-CARS))
 (16 16 (:REWRITE DEFAULT-<-2))
 (16 16 (:REWRITE DEFAULT-<-1))
 (16 8 (:REWRITE DEFAULT-+-2))
 (16 4 (:DEFINITION ENDP))
 (16 2 (:REWRITE NOT-IN-TEST-FOR-ALL-CDR))
 (13 13 (:REWRITE VALIDFIELDS-TRLST-TEST-FOR-ALL-SUBSET))
 (12 12 (:TYPE-PRESCRIPTION WEAK-V-P))
 (12 12 (:TYPE-PRESCRIPTION PER-RESOURCE-NO-DUPLICATE-FLITS))
 (12 12 (:REWRITE NATP-FOR-ALL-SUBSET-APPEND))
 (12 12 (:REWRITE NATP-FOR-ALL-SUBSET))
 (12 12 (:REWRITE NATP-FOR-ALL-HOLDS-FOR-ASSOC))
 (12 12 (:REWRITE LEN=-FOR-ALL-SUBSET-APPEND))
 (12 12 (:REWRITE LEN=-FOR-ALL-SUBSET))
 (12 4 (:REWRITE DEFS-V-P-INCLUDES-WEAK-V-P))
 (8 8 (:TYPE-PRESCRIPTION V-P))
 (8 8 (:TYPE-PRESCRIPTION FILTER-CAR=-TEST-FILTER-TRUE-LISTP))
 (8 8 (:REWRITE DEFAULT-+-1))
 (8 4 (:DEFINITION FILTER-CAR=-TEST))
 (6 6 (:REWRITE SUBSET-NOT-IN))
 (6 6 (:REWRITE NOT-IN-TEST-FOR-ALL-SUBSET-APPEND))
 (6 6 (:REWRITE NOT-IN-TEST-FOR-ALL-SUBSET))
 (4 4 (:REWRITE VALIDFIELDS-TRLST-TEST-FOR-ALL-HOLDS-FOR-ASSOC))
 (4 4 (:REWRITE LEN=-FOR-ALL-HOLDS-FOR-MEMBER))
 (4 4 (:REWRITE LEN=-FOR-ALL-HOLDS-FOR-ASSOC))
 (2 2 (:REWRITE V-ID-MAP-SUBSETP-IMPLIES-MEMBER-V))
 (2 2 (:REWRITE NOT-IN-TEST-FOR-ALL-HOLDS-FOR-MEMBER))
 (2 2 (:REWRITE NOT-IN-TEST-FOR-ALL-HOLDS-FOR-ASSOC))
 (2 1 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (1 1 (:TYPE-PRESCRIPTION CONSP-APPEND . 2))
 (1 1 (:TYPE-PRESCRIPTION CONSP-APPEND . 1))
 (1 1 (:TYPE-PRESCRIPTION BINARY-APPEND))
 )
(FWD-TRLSTP
 (242 1 (:DEFINITION VALIDFIELDS-TRLST))
 (216 1 (:DEFINITION VALIDFIELDS-TRLST-TEST))
 (147 1 (:DEFINITION VALIDFIELD-TRAVELP))
 (112 1 (:DEFINITION VALIDFIELD-LOC))
 (48 8 (:DEFINITION MEMBER-EQUAL))
 (37 3 (:REWRITE NATP-FOR-ALL-HOLDS-FOR-MEMBER))
 (32 19 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (31 31 (:REWRITE DEFAULT-CDR))
 (31 31 (:REWRITE DEFAULT-CAR))
 (30 2 (:DEFINITION SUBSETP-EQUAL))
 (30 1 (:DEFINITION PER-RESOURCE-NO-DUPLICATE-FLITS))
 (24 2 (:DEFINITION NO-DUPLICATESP-EQUAL))
 (21 1 (:DEFINITION A-LEN=))
 (18 18 (:TYPE-PRESCRIPTION CADRS))
 (18 1 (:DEFINITION A-NATP))
 (16 16 (:REWRITE SUBSETP-CONS-CAR-PART))
 (12 2 (:DEFINITION CADRS))
 (10 2 (:DEFINITION LEN))
 (9 3 (:DEFINITION NATP))
 (8 2 (:DEFINITION STRIP-CARS))
 (7 7 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (7 7 (:TYPE-PRESCRIPTION LEN))
 (7 7 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (7 1 (:DEFINITION LEN=))
 (6 6 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (6 6 (:TYPE-PRESCRIPTION A-NATP))
 (6 6 (:TYPE-PRESCRIPTION A-LEN=))
 (6 3 (:DEFINITION TRUE-LISTP))
 (6 1 (:REWRITE VALIDFIELDS-TRLST-TEST-FOR-ALL-CDR))
 (6 1 (:REWRITE NATP-FOR-ALL-CDR))
 (6 1 (:REWRITE LEN=-FOR-ALL-CDR))
 (6 1 (:DEFINITION FILTER-CAR=-ALT))
 (4 4 (:TYPE-PRESCRIPTION STRIP-CARS))
 (4 4 (:REWRITE SUBSETP-TRANS))
 (4 4 (:REWRITE SUBSETP-CONS-CDR-PART))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 2 (:REWRITE DEFAULT-+-2))
 (3 3 (:TYPE-PRESCRIPTION WEAK-V-P))
 (3 3 (:TYPE-PRESCRIPTION PER-RESOURCE-NO-DUPLICATE-FLITS))
 (3 3 (:REWRITE VALIDFIELDS-TRLST-TEST-FOR-ALL-SUBSET-APPEND))
 (3 3 (:REWRITE VALIDFIELDS-TRLST-TEST-FOR-ALL-SUBSET))
 (3 3 (:REWRITE NATP-FOR-ALL-SUBSET-APPEND))
 (3 3 (:REWRITE NATP-FOR-ALL-SUBSET))
 (3 3 (:REWRITE NATP-FOR-ALL-HOLDS-FOR-ASSOC))
 (3 3 (:REWRITE LEN=-FOR-ALL-SUBSET-APPEND))
 (3 3 (:REWRITE LEN=-FOR-ALL-SUBSET))
 (3 1 (:REWRITE DEFS-V-P-INCLUDES-WEAK-V-P))
 (3 1 (:DEFINITION V-IDS))
 (2 2 (:TYPE-PRESCRIPTION V-P))
 (2 2 (:TYPE-PRESCRIPTION V-ID-MAP-TRUE-LISTP))
 (2 2 (:TYPE-PRESCRIPTION FILTER-CAR=-TEST-FILTER-TRUE-LISTP))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 1 (:DEFINITION FILTER-CAR=-TEST))
 (1 1 (:REWRITE VALIDFIELDS-TRLST-TEST-FOR-ALL-HOLDS-FOR-MEMBER))
 (1 1 (:REWRITE VALIDFIELDS-TRLST-TEST-FOR-ALL-HOLDS-FOR-ASSOC))
 (1 1 (:REWRITE LEN=-FOR-ALL-HOLDS-FOR-MEMBER))
 (1 1 (:REWRITE LEN=-FOR-ALL-HOLDS-FOR-ASSOC))
 )
(REV)
(SUBSETP-REV-L
 (86 43 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (43 43 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (29 27 (:REWRITE DEFAULT-CAR))
 (22 22 (:REWRITE SUBSETP-CONS-CAR-PART))
 (20 19 (:REWRITE DEFAULT-CDR))
 (17 17 (:REWRITE SUBSETP-TRANS))
 (17 17 (:REWRITE SUBSETP-CONS-CDR-PART))
 )
(MEMBER-REV
 (108 108 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (34 34 (:REWRITE SUBSETP-CONS-CAR-PART))
 (33 30 (:REWRITE DEFAULT-CAR))
 (21 19 (:REWRITE DEFAULT-CDR))
 )
(SUBSETP-REV-R
 (84 42 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (42 42 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (30 5 (:DEFINITION REV))
 (25 25 (:REWRITE DEFAULT-CAR))
 (20 20 (:REWRITE SUBSETP-CONS-CAR-PART))
 (19 19 (:REWRITE DEFAULT-CDR))
 (15 5 (:REWRITE PERMP-APPEND-CONS))
 (14 14 (:REWRITE SUBSETP-TRANS))
 (14 14 (:REWRITE SUBSETP-CONS-CDR-PART))
 (10 5 (:REWRITE APPEND-RIGHT-ID))
 )
(VALIDSTATE-ENTRY-IMPLIES-COORD-AND-BUFFER
 (10 10 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE VALIDCOORD-FOR-ALL-HOLDS-FOR-MEMBER))
 (2 2 (:REWRITE VALIDCOORD-FOR-ALL-HOLDS-FOR-ASSOC))
 (2 2 (:REWRITE VALIDBUFFER-FOR-ALL-HOLDS-FOR-MEMBER))
 (2 2 (:REWRITE VALIDBUFFER-FOR-ALL-HOLDS-FOR-ASSOC))
 (1 1 (:REWRITE VALIDSTATE-ENTRYP-FOR-ALL-HOLDS-FOR-MEMBER))
 (1 1 (:REWRITE VALIDSTATE-ENTRYP-FOR-ALL-HOLDS-FOR-ASSOC))
 )
