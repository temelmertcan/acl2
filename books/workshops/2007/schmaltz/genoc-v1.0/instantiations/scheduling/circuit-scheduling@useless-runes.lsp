(REV)
(CONSUME-ATTEMPTS
 (396 24 (:DEFINITION INTEGER-ABS))
 (390 28 (:REWRITE NOTLESSP-IMPLIES-NOT-<-CAR))
 (373 56 (:REWRITE LESSP-IMPLIES-<-CAR))
 (360 14 (:DEFINITION NOTLESSP))
 (304 25 (:DEFINITION LESSP))
 (260 130 (:REWRITE DEFAULT-+-2))
 (184 130 (:REWRITE DEFAULT-+-1))
 (144 144 (:TYPE-PRESCRIPTION LESSP))
 (106 106 (:REWRITE DEFAULT-CDR))
 (106 87 (:REWRITE DEFAULT-<-1))
 (100 87 (:REWRITE DEFAULT-<-2))
 (96 12 (:DEFINITION LENGTH))
 (92 92 (:REWRITE DEFAULT-CAR))
 (87 87 (:REWRITE LESSP-IMPLIES-<))
 (78 78 (:TYPE-PRESCRIPTION NOTLESSP))
 (60 12 (:DEFINITION LEN))
 (59 59 (:REWRITE NOTLESSP-IMPLIES-NOT-<))
 (33 33 (:REWRITE FOLD-CONSTS-IN-+))
 (24 24 (:REWRITE DEFAULT-UNARY-MINUS))
 (13 13 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (12 12 (:TYPE-PRESCRIPTION LEN))
 (12 12 (:REWRITE DEFAULT-REALPART))
 (12 12 (:REWRITE DEFAULT-NUMERATOR))
 (12 12 (:REWRITE DEFAULT-IMAGPART))
 (12 12 (:REWRITE DEFAULT-DENOMINATOR))
 (12 12 (:REWRITE DEFAULT-COERCE-2))
 (12 12 (:REWRITE DEFAULT-COERCE-1))
 (1 1 (:TYPE-PRESCRIPTION CONSUME-ATTEMPTS))
 )
(TEST_PREV_ROUTES)
(UPDATE_ROUTE)
(CT-SCHEDULER
 (6 3 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (3 3 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (3 3 (:TYPE-PRESCRIPTION CONSP-APPEND . 2))
 (3 3 (:TYPE-PRESCRIPTION CONSP-APPEND . 1))
 (3 3 (:TYPE-PRESCRIPTION BINARY-APPEND))
 )
(CIRCUIT-SCHEDULING
 (1 1 (:TYPE-PRESCRIPTION CONSUME-ATTEMPTS))
 )
(CT-SCHED-NT-SCHED
 (2 1 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (1 1 (:TYPE-PRESCRIPTION CONSP-APPEND . 2))
 (1 1 (:TYPE-PRESCRIPTION CONSP-APPEND . 1))
 (1 1 (:TYPE-PRESCRIPTION BINARY-APPEND))
 )
(SCHEDULER-=-NON-TAIL-SCHEDULED
 (1506 98 (:REWRITE NTH-WITH-LARGE-INDEX))
 (931 49 (:DEFINITION NTH))
 (528 528 (:TYPE-PRESCRIPTION LEN))
 (440 88 (:DEFINITION LEN))
 (332 332 (:REWRITE DEFAULT-CDR))
 (327 35 (:DEFINITION NO_INTERSECTP))
 (241 235 (:REWRITE DEFAULT-CAR))
 (176 88 (:REWRITE DEFAULT-<-2))
 (176 88 (:REWRITE DEFAULT-+-2))
 (174 157 (:TYPE-PRESCRIPTION CONSP-APPEND . 1))
 (138 6 (:REWRITE NO_INTERSECTP_APPEND))
 (111 35 (:DEFINITION MEMBER-EQUAL))
 (88 88 (:TYPE-PRESCRIPTION NFIX))
 (88 88 (:REWRITE NOTLESSP-IMPLIES-NOT-<))
 (88 88 (:REWRITE LESSP-IMPLIES-<))
 (88 88 (:REWRITE DEFAULT-<-1))
 (88 88 (:REWRITE DEFAULT-+-1))
 (88 88 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (70 35 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (35 35 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (35 35 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (12 12 (:REWRITE CHECKROUTES-CAAR))
 )
(CT-SCHED-NT-DEL
 (8 4 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (4 4 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (4 4 (:TYPE-PRESCRIPTION CONSP-APPEND . 2))
 (4 4 (:TYPE-PRESCRIPTION CONSP-APPEND . 1))
 (4 4 (:TYPE-PRESCRIPTION BINARY-APPEND))
 )
(SCHEDULER-=-NON-TAIL-DELAYED
 (956 60 (:REWRITE NTH-WITH-LARGE-INDEX))
 (570 30 (:DEFINITION NTH))
 (336 336 (:TYPE-PRESCRIPTION LEN))
 (280 56 (:DEFINITION LEN))
 (258 252 (:REWRITE DEFAULT-CDR))
 (233 25 (:DEFINITION NO_INTERSECTP))
 (175 175 (:REWRITE DEFAULT-CAR))
 (174 157 (:TYPE-PRESCRIPTION CONSP-APPEND . 1))
 (112 56 (:REWRITE DEFAULT-<-2))
 (112 56 (:REWRITE DEFAULT-+-2))
 (92 4 (:REWRITE NO_INTERSECTP_APPEND))
 (79 25 (:DEFINITION MEMBER-EQUAL))
 (56 56 (:TYPE-PRESCRIPTION NFIX))
 (56 56 (:REWRITE NOTLESSP-IMPLIES-NOT-<))
 (56 56 (:REWRITE LESSP-IMPLIES-<))
 (56 56 (:REWRITE DEFAULT-<-1))
 (56 56 (:REWRITE DEFAULT-+-1))
 (56 56 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (50 25 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (25 25 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (25 25 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (8 8 (:REWRITE CHECKROUTES-CAAR))
 )
(CONSUME-AT-LEAST-ONE-ATTEMPT-CIRCUIT-SCHEDULING
 (991 70 (:REWRITE NOTLESSP-IMPLIES-NOT-<-CAR))
 (960 140 (:REWRITE LESSP-IMPLIES-<-CAR))
 (874 39 (:DEFINITION NOTLESSP))
 (758 70 (:DEFINITION LESSP))
 (388 388 (:TYPE-PRESCRIPTION LESSP))
 (272 16 (:REWRITE NTH-WITH-LARGE-INDEX))
 (265 261 (:REWRITE DEFAULT-CDR))
 (263 259 (:REWRITE DEFAULT-CAR))
 (240 2 (:DEFINITION CT-SCHED-NT-SCHED))
 (226 226 (:TYPE-PRESCRIPTION NOTLESSP))
 (209 188 (:REWRITE DEFAULT-<-2))
 (198 188 (:REWRITE DEFAULT-<-1))
 (188 188 (:REWRITE LESSP-IMPLIES-<))
 (185 5 (:DEFINITION ROUTESV))
 (165 112 (:REWRITE DEFAULT-+-2))
 (160 2 (:DEFINITION CT-SCHED-NT-DEL))
 (152 8 (:DEFINITION NTH))
 (139 112 (:REWRITE DEFAULT-+-1))
 (120 3 (:DEFINITION UPDATE_ROUTE))
 (120 1 (:DEFINITION CT-SCHEDULER))
 (118 118 (:REWRITE NOTLESSP-IMPLIES-NOT-<))
 (111 3 (:DEFINITION FRMV))
 (100 100 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (100 20 (:DEFINITION TRUE-LISTP))
 (96 96 (:TYPE-PRESCRIPTION LEN))
 (80 16 (:DEFINITION LEN))
 (80 10 (:REWRITE APPEND-TO-NIL))
 (80 10 (:REWRITE APPEND-RIGHT-ID))
 (62 62 (:TYPE-PRESCRIPTION CONSUME-ATTEMPTS))
 (20 5 (:DEFINITION TEST_PREV_ROUTES))
 (16 16 (:TYPE-PRESCRIPTION NFIX))
 (16 16 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (10 5 (:REWRITE COMMUTATIVITY_NO_INTERSECTP))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (6 3 (:DEFINITION IDV))
 (5 5 (:DEFINITION NO_INTERSECTP))
 )
(SUBSETP-SCHEDULED-CT
 (2624 160 (:REWRITE NTH-WITH-LARGE-INDEX))
 (1520 80 (:DEFINITION NTH))
 (924 924 (:TYPE-PRESCRIPTION LEN))
 (770 154 (:DEFINITION LEN))
 (707 697 (:REWRITE DEFAULT-CDR))
 (481 51 (:DEFINITION NO_INTERSECTP))
 (453 445 (:REWRITE DEFAULT-CAR))
 (335 181 (:REWRITE DEFAULT-<-2))
 (308 154 (:REWRITE DEFAULT-+-2))
 (253 11 (:REWRITE NO_INTERSECTP_APPEND))
 (181 181 (:REWRITE LESSP-IMPLIES-<))
 (181 181 (:REWRITE DEFAULT-<-1))
 (172 172 (:REWRITE NOTLESSP-IMPLIES-NOT-<))
 (154 154 (:TYPE-PRESCRIPTION NFIX))
 (154 154 (:REWRITE DEFAULT-+-1))
 (154 154 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (144 18 (:REWRITE NOTLESSP-IMPLIES-NOT-<-CAR))
 (135 27 (:REWRITE LESSP-IMPLIES-<-CAR))
 (117 9 (:DEFINITION NOTLESSP))
 (99 9 (:DEFINITION LESSP))
 (54 54 (:TYPE-PRESCRIPTION NOTLESSP))
 (54 54 (:TYPE-PRESCRIPTION LESSP))
 (51 51 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (37 37 (:REWRITE CHECKROUTES-CAAR))
 (36 9 (:DEFINITION VALIDFIELD-ROUTE))
 )
(SUBSETP-DELAYED-CT
 (1670 102 (:REWRITE NTH-WITH-LARGE-INDEX))
 (969 51 (:DEFINITION NTH))
 (588 588 (:TYPE-PRESCRIPTION LEN))
 (580 570 (:REWRITE DEFAULT-CDR))
 (490 98 (:DEFINITION LEN))
 (389 381 (:REWRITE DEFAULT-CAR))
 (385 41 (:DEFINITION NO_INTERSECTP))
 (223 125 (:REWRITE DEFAULT-<-2))
 (196 98 (:REWRITE DEFAULT-+-2))
 (184 8 (:REWRITE NO_INTERSECTP_APPEND))
 (144 18 (:REWRITE NOTLESSP-IMPLIES-NOT-<-CAR))
 (135 27 (:REWRITE LESSP-IMPLIES-<-CAR))
 (125 125 (:REWRITE LESSP-IMPLIES-<))
 (125 125 (:REWRITE DEFAULT-<-1))
 (117 9 (:DEFINITION NOTLESSP))
 (116 116 (:REWRITE NOTLESSP-IMPLIES-NOT-<))
 (99 9 (:DEFINITION LESSP))
 (98 98 (:TYPE-PRESCRIPTION NFIX))
 (98 98 (:REWRITE DEFAULT-+-1))
 (98 98 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (54 54 (:TYPE-PRESCRIPTION NOTLESSP))
 (54 54 (:TYPE-PRESCRIPTION LESSP))
 (41 41 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (36 9 (:DEFINITION VALIDFIELD-ROUTE))
 (31 31 (:REWRITE CHECKROUTES-CAAR))
 )
(VALIDFIELD-ROUTE-TEST_PREV_ROUTES
 (90 90 (:REWRITE DEFAULT-CDR))
 (83 83 (:REWRITE DEFAULT-CAR))
 (64 22 (:DEFINITION MEMBER-EQUAL))
 (42 21 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (21 21 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(VALIDFIELDS-TRLST-CT-SCHED
 (2740 173 (:REWRITE NTH-WITH-LARGE-INDEX))
 (1326 216 (:DEFINITION LEN))
 (856 850 (:REWRITE DEFAULT-CDR))
 (511 42 (:REWRITE NOTLESSP-IMPLIES-NOT-<-CAR))
 (484 81 (:REWRITE LESSP-IMPLIES-<-CAR))
 (462 21 (:DEFINITION NOTLESSP))
 (421 416 (:REWRITE DEFAULT-CAR))
 (404 31 (:DEFINITION LESSP))
 (330 165 (:REWRITE DEFAULT-+-2))
 (319 200 (:REWRITE DEFAULT-<-2))
 (313 31 (:DEFINITION NO_INTERSECTP))
 (216 200 (:REWRITE DEFAULT-<-1))
 (200 200 (:REWRITE LESSP-IMPLIES-<))
 (165 165 (:REWRITE DEFAULT-+-1))
 (161 161 (:REWRITE NOTLESSP-IMPLIES-NOT-<))
 (138 138 (:TYPE-PRESCRIPTION LESSP))
 (129 11 (:DEFINITION BINARY-APPEND))
 (123 31 (:DEFINITION MEMBER-EQUAL))
 (119 119 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (118 4 (:REWRITE NO_INTERSECTP_APPEND))
 (110 110 (:TYPE-PRESCRIPTION NOTLESSP))
 (62 31 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (34 17 (:DEFINITION TRUE-LISTP))
 (31 31 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (16 16 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (8 8 (:REWRITE CHECKROUTES-CAAR))
 )
(NOT-MEMBER-V-IDS-CT-SCHED
 (1740 108 (:REWRITE NTH-WITH-LARGE-INDEX))
 (1026 54 (:DEFINITION NTH))
 (612 612 (:TYPE-PRESCRIPTION LEN))
 (546 46 (:DEFINITION NO_INTERSECTP))
 (510 102 (:DEFINITION LEN))
 (492 486 (:REWRITE DEFAULT-CDR))
 (400 40 (:REWRITE VALIDFIELD-ROUTE-TEST_PREV_ROUTES))
 (363 11 (:REWRITE NO_INTERSECTP_APPEND))
 (349 343 (:REWRITE DEFAULT-CAR))
 (280 40 (:DEFINITION VALIDFIELD-ROUTE))
 (204 102 (:REWRITE DEFAULT-<-2))
 (204 102 (:REWRITE DEFAULT-+-2))
 (200 200 (:TYPE-PRESCRIPTION VALIDFIELD-ROUTE))
 (102 102 (:TYPE-PRESCRIPTION NFIX))
 (102 102 (:REWRITE NOTLESSP-IMPLIES-NOT-<))
 (102 102 (:REWRITE LESSP-IMPLIES-<))
 (102 102 (:REWRITE DEFAULT-<-1))
 (102 102 (:REWRITE DEFAULT-+-1))
 (102 102 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (46 46 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (46 46 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (22 22 (:REWRITE CHECKROUTES-CAAR))
 )
(NO-DUPLICATESP-CT-SCHED
 (1740 108 (:REWRITE NTH-WITH-LARGE-INDEX))
 (1026 54 (:DEFINITION NTH))
 (612 612 (:TYPE-PRESCRIPTION LEN))
 (546 46 (:DEFINITION NO_INTERSECTP))
 (530 519 (:REWRITE DEFAULT-CDR))
 (510 102 (:DEFINITION LEN))
 (400 40 (:REWRITE VALIDFIELD-ROUTE-TEST_PREV_ROUTES))
 (363 11 (:REWRITE NO_INTERSECTP_APPEND))
 (362 356 (:REWRITE DEFAULT-CAR))
 (328 63 (:DEFINITION MEMBER-EQUAL))
 (280 40 (:DEFINITION VALIDFIELD-ROUTE))
 (204 102 (:REWRITE DEFAULT-<-2))
 (204 102 (:REWRITE DEFAULT-+-2))
 (200 200 (:TYPE-PRESCRIPTION VALIDFIELD-ROUTE))
 (102 102 (:TYPE-PRESCRIPTION NFIX))
 (102 102 (:REWRITE NOTLESSP-IMPLIES-NOT-<))
 (102 102 (:REWRITE LESSP-IMPLIES-<))
 (102 102 (:REWRITE DEFAULT-<-1))
 (102 102 (:REWRITE DEFAULT-+-1))
 (102 102 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (46 46 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (46 46 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (34 34 (:REWRITE CHECKROUTES-CAAR))
 )
(CONS-V-IDS
 (15 15 (:REWRITE DEFAULT-CAR))
 (8 8 (:REWRITE DEFAULT-CDR))
 )
(TRLSTP-SCHEDULED-CT
 (324 3 (:DEFINITION CT-SCHED-NT-SCHED))
 (272 16 (:REWRITE NTH-WITH-LARGE-INDEX))
 (247 7 (:DEFINITION BINARY-APPEND))
 (244 2 (:DEFINITION V-IDS))
 (152 8 (:DEFINITION NTH))
 (148 4 (:DEFINITION ROUTESV))
 (148 4 (:DEFINITION FRMV))
 (135 1 (:DEFINITION VALIDFIELDS-TRLST))
 (120 3 (:DEFINITION UPDATE_ROUTE))
 (96 96 (:TYPE-PRESCRIPTION LEN))
 (80 16 (:DEFINITION LEN))
 (77 74 (:REWRITE DEFAULT-CDR))
 (43 40 (:REWRITE DEFAULT-CAR))
 (42 3 (:DEFINITION TEST_PREV_ROUTES))
 (35 19 (:REWRITE DEFAULT-<-2))
 (35 1 (:DEFINITION NATP))
 (32 16 (:REWRITE DEFAULT-+-2))
 (30 3 (:REWRITE VALIDFIELD-ROUTE-TEST_PREV_ROUTES))
 (30 3 (:REWRITE COMMUTATIVITY_NO_INTERSECTP))
 (27 3 (:DEFINITION NO_INTERSECTP))
 (25 4 (:DEFINITION VALIDFIELD-ROUTE))
 (22 1 (:DEFINITION NO-DUPLICATESP-EQUAL))
 (19 19 (:REWRITE LESSP-IMPLIES-<))
 (19 19 (:REWRITE DEFAULT-<-1))
 (18 18 (:REWRITE NOTLESSP-IMPLIES-NOT-<))
 (18 1 (:DEFINITION VALIDFIELD-TRAVELP))
 (17 17 (:TYPE-PRESCRIPTION VALIDFIELD-ROUTE))
 (16 16 (:TYPE-PRESCRIPTION NFIX))
 (16 16 (:REWRITE DEFAULT-+-1))
 (16 16 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (16 4 (:DEFINITION MEMBER-EQUAL))
 (16 2 (:REWRITE NOTLESSP-IMPLIES-NOT-<-CAR))
 (15 3 (:REWRITE LESSP-IMPLIES-<-CAR))
 (13 1 (:DEFINITION NOTLESSP))
 (11 11 (:TYPE-PRESCRIPTION V-IDS))
 (11 1 (:DEFINITION LESSP))
 (9 4 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (8 4 (:DEFINITION IDV))
 (6 6 (:TYPE-PRESCRIPTION NOTLESSP))
 (6 6 (:TYPE-PRESCRIPTION LESSP))
 (4 2 (:DEFINITION TRUE-LISTP))
 (3 3 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (3 3 (:TYPE-PRESCRIPTION NO_INTERSECTP))
 (3 3 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (3 3 (:REWRITE CONS-V-IDS))
 (2 2 (:REWRITE CDR-CONS))
 (2 2 (:REWRITE CAR-CONS))
 )
(VALIDFIELDS-TRLST-CT-DEL
 (1224 72 (:REWRITE NTH-WITH-LARGE-INDEX))
 (432 432 (:TYPE-PRESCRIPTION LEN))
 (370 369 (:REWRITE DEFAULT-CDR))
 (360 72 (:DEFINITION LEN))
 (181 22 (:REWRITE NOTLESSP-IMPLIES-NOT-<-CAR))
 (177 105 (:REWRITE DEFAULT-<-2))
 (170 33 (:REWRITE LESSP-IMPLIES-<-CAR))
 (151 150 (:REWRITE DEFAULT-CAR))
 (150 14 (:DEFINITION NO_INTERSECTP))
 (148 11 (:DEFINITION NOTLESSP))
 (144 72 (:REWRITE DEFAULT-+-2))
 (126 11 (:DEFINITION LESSP))
 (105 105 (:REWRITE LESSP-IMPLIES-<))
 (105 105 (:REWRITE DEFAULT-<-1))
 (94 94 (:REWRITE NOTLESSP-IMPLIES-NOT-<))
 (91 7 (:DEFINITION BINARY-APPEND))
 (90 9 (:REWRITE VALIDFIELD-ROUTE-TEST_PREV_ROUTES))
 (72 72 (:TYPE-PRESCRIPTION NFIX))
 (72 72 (:REWRITE DEFAULT-+-1))
 (72 72 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (66 66 (:TYPE-PRESCRIPTION NOTLESSP))
 (66 66 (:TYPE-PRESCRIPTION LESSP))
 (66 2 (:REWRITE NO_INTERSECTP_APPEND))
 (64 14 (:DEFINITION MEMBER-EQUAL))
 (28 14 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (22 11 (:DEFINITION TRUE-LISTP))
 (14 14 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (14 14 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (4 4 (:REWRITE CHECKROUTES-CAAR))
 )
(NOT-MEMBER-V-IDS-CT-DEL
 (888 56 (:REWRITE NTH-WITH-LARGE-INDEX))
 (532 28 (:DEFINITION NTH))
 (420 36 (:DEFINITION NO_INTERSECTP))
 (389 350 (:REWRITE DEFAULT-CDR))
 (312 312 (:TYPE-PRESCRIPTION LEN))
 (312 273 (:REWRITE DEFAULT-CAR))
 (310 31 (:REWRITE VALIDFIELD-ROUTE-TEST_PREV_ROUTES))
 (264 8 (:REWRITE NO_INTERSECTP_APPEND))
 (260 52 (:DEFINITION LEN))
 (217 31 (:DEFINITION VALIDFIELD-ROUTE))
 (155 155 (:TYPE-PRESCRIPTION VALIDFIELD-ROUTE))
 (104 52 (:REWRITE DEFAULT-<-2))
 (104 52 (:REWRITE DEFAULT-+-2))
 (52 52 (:TYPE-PRESCRIPTION NFIX))
 (52 52 (:REWRITE NOTLESSP-IMPLIES-NOT-<))
 (52 52 (:REWRITE LESSP-IMPLIES-<))
 (52 52 (:REWRITE DEFAULT-<-1))
 (52 52 (:REWRITE DEFAULT-+-1))
 (52 52 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (36 36 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (36 36 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (16 16 (:REWRITE CHECKROUTES-CAAR))
 )
(NO-DUPLICATESP-CT-DEL
 (888 56 (:REWRITE NTH-WITH-LARGE-INDEX))
 (532 28 (:DEFINITION NTH))
 (445 383 (:REWRITE DEFAULT-CDR))
 (420 36 (:DEFINITION NO_INTERSECTP))
 (357 53 (:DEFINITION MEMBER-EQUAL))
 (343 286 (:REWRITE DEFAULT-CAR))
 (312 312 (:TYPE-PRESCRIPTION LEN))
 (310 31 (:REWRITE VALIDFIELD-ROUTE-TEST_PREV_ROUTES))
 (264 8 (:REWRITE NO_INTERSECTP_APPEND))
 (260 52 (:DEFINITION LEN))
 (217 31 (:DEFINITION VALIDFIELD-ROUTE))
 (155 155 (:TYPE-PRESCRIPTION VALIDFIELD-ROUTE))
 (104 52 (:REWRITE DEFAULT-<-2))
 (104 52 (:REWRITE DEFAULT-+-2))
 (52 52 (:TYPE-PRESCRIPTION NFIX))
 (52 52 (:REWRITE NOTLESSP-IMPLIES-NOT-<))
 (52 52 (:REWRITE LESSP-IMPLIES-<))
 (52 52 (:REWRITE DEFAULT-<-1))
 (52 52 (:REWRITE DEFAULT-+-1))
 (52 52 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (36 36 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (36 36 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (28 28 (:REWRITE CHECKROUTES-CAAR))
 )
(TRLSTP-DELAYED-CT
 (204 3 (:DEFINITION CT-SCHED-NT-DEL))
 (170 10 (:REWRITE NTH-WITH-LARGE-INDEX))
 (167 7 (:DEFINITION BINARY-APPEND))
 (164 2 (:DEFINITION V-IDS))
 (148 4 (:DEFINITION ROUTESV))
 (135 1 (:DEFINITION VALIDFIELDS-TRLST))
 (95 5 (:DEFINITION NTH))
 (68 65 (:REWRITE DEFAULT-CDR))
 (60 60 (:TYPE-PRESCRIPTION LEN))
 (50 10 (:DEFINITION LEN))
 (42 3 (:DEFINITION TEST_PREV_ROUTES))
 (40 37 (:REWRITE DEFAULT-CAR))
 (37 1 (:DEFINITION FRMV))
 (35 1 (:DEFINITION NATP))
 (30 3 (:REWRITE VALIDFIELD-ROUTE-TEST_PREV_ROUTES))
 (30 3 (:REWRITE COMMUTATIVITY_NO_INTERSECTP))
 (27 3 (:DEFINITION NO_INTERSECTP))
 (25 4 (:DEFINITION VALIDFIELD-ROUTE))
 (23 13 (:REWRITE DEFAULT-<-2))
 (22 1 (:DEFINITION NO-DUPLICATESP-EQUAL))
 (20 10 (:REWRITE DEFAULT-+-2))
 (18 1 (:DEFINITION VALIDFIELD-TRAVELP))
 (17 17 (:TYPE-PRESCRIPTION VALIDFIELD-ROUTE))
 (16 4 (:DEFINITION MEMBER-EQUAL))
 (16 2 (:REWRITE NOTLESSP-IMPLIES-NOT-<-CAR))
 (15 3 (:REWRITE LESSP-IMPLIES-<-CAR))
 (13 13 (:REWRITE LESSP-IMPLIES-<))
 (13 13 (:REWRITE DEFAULT-<-1))
 (13 1 (:DEFINITION NOTLESSP))
 (12 12 (:REWRITE NOTLESSP-IMPLIES-NOT-<))
 (11 11 (:TYPE-PRESCRIPTION V-IDS))
 (11 1 (:DEFINITION LESSP))
 (10 10 (:TYPE-PRESCRIPTION NFIX))
 (10 10 (:REWRITE DEFAULT-+-1))
 (10 10 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (9 4 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (6 6 (:TYPE-PRESCRIPTION NOTLESSP))
 (6 6 (:TYPE-PRESCRIPTION LESSP))
 (4 2 (:DEFINITION TRUE-LISTP))
 (3 3 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (3 3 (:TYPE-PRESCRIPTION NO_INTERSECTP))
 (3 3 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (3 3 (:REWRITE CONS-V-IDS))
 (2 2 (:REWRITE CDR-CONS))
 (2 2 (:REWRITE CAR-CONS))
 (2 1 (:DEFINITION IDV))
 )
(EXTRACT-SUBLST-CONS
 (931 30 (:REWRITE MEMBER-EQUAL-M-IDS-ASSOC-EQUAL))
 (453 33 (:DEFINITION M-IDS))
 (430 242 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (270 267 (:REWRITE DEFAULT-CAR))
 (206 206 (:TYPE-PRESCRIPTION M-IDS))
 (184 181 (:REWRITE DEFAULT-CDR))
 (101 101 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(TEST_PREV_ROUTES-MEMBER-EQUAL
 (299 151 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (148 148 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (55 55 (:REWRITE DEFAULT-CAR))
 (36 36 (:REWRITE DEFAULT-CDR))
 )
(CT-SCHEDULED-CORRECTNESS
 (31758 1937 (:REWRITE NTH-WITH-LARGE-INDEX))
 (13709 966 (:DEFINITION MEMBER-EQUAL))
 (11805 97 (:REWRITE MEMBER-EQUAL-M-IDS-ASSOC-EQUAL))
 (10431 9894 (:REWRITE DEFAULT-CDR))
 (9873 1910 (:DEFINITION LEN))
 (9192 832 (:DEFINITION NO_INTERSECTP))
 (7137 6534 (:REWRITE DEFAULT-CAR))
 (6450 226 (:REWRITE NO_INTERSECTP_APPEND))
 (6064 1384 (:REWRITE VALIDFIELD-ROUTE-TEST_PREV_ROUTES))
 (3799 1980 (:REWRITE DEFAULT-<-2))
 (3740 545 (:DEFINITION VALIDFIELD-ROUTE))
 (3722 1861 (:REWRITE DEFAULT-+-2))
 (2028 1980 (:REWRITE DEFAULT-<-1))
 (1980 1980 (:REWRITE LESSP-IMPLIES-<))
 (1891 1891 (:REWRITE NOTLESSP-IMPLIES-NOT-<))
 (1861 1861 (:REWRITE DEFAULT-+-1))
 (1819 1819 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (1408 92 (:DEFINITION M-IDS))
 (1064 70 (:REWRITE NOTLESSP-IMPLIES-NOT-<-CAR))
 (1011 159 (:REWRITE LESSP-IMPLIES-<-CAR))
 (1001 35 (:DEFINITION NOTLESSP))
 (883 65 (:DEFINITION LESSP))
 (855 855 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (562 562 (:TYPE-PRESCRIPTION M-IDS))
 (477 477 (:REWRITE CHECKROUTES-CAAR))
 (246 246 (:TYPE-PRESCRIPTION LESSP))
 (183 159 (:REWRITE CONS-V-IDS))
 (162 162 (:TYPE-PRESCRIPTION NOTLESSP))
 (48 48 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(CT-DELAYED-CORRECTNESS
 (13574 846 (:REWRITE NTH-WITH-LARGE-INDEX))
 (9455 811 (:DEFINITION MEMBER-EQUAL))
 (8204 93 (:REWRITE MEMBER-EQUAL-M-IDS-ASSOC-EQUAL))
 (7810 7346 (:REWRITE DEFAULT-CDR))
 (7560 704 (:DEFINITION NO_INTERSECTP))
 (5778 5317 (:REWRITE DEFAULT-CAR))
 (5130 186 (:REWRITE NO_INTERSECTP_APPEND))
 (4864 1264 (:REWRITE VALIDFIELD-ROUTE-TEST_PREV_ROUTES))
 (4203 847 (:DEFINITION LEN))
 (2900 425 (:DEFINITION VALIDFIELD-ROUTE))
 (1695 928 (:REWRITE DEFAULT-<-2))
 (1606 803 (:REWRITE DEFAULT-+-2))
 (1332 87 (:DEFINITION M-IDS))
 (1064 70 (:REWRITE NOTLESSP-IMPLIES-NOT-<-CAR))
 (1011 159 (:REWRITE LESSP-IMPLIES-<-CAR))
 (1001 35 (:DEFINITION NOTLESSP))
 (976 928 (:REWRITE DEFAULT-<-1))
 (928 928 (:REWRITE LESSP-IMPLIES-<))
 (883 65 (:DEFINITION LESSP))
 (839 839 (:REWRITE NOTLESSP-IMPLIES-NOT-<))
 (803 803 (:REWRITE DEFAULT-+-1))
 (767 767 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (704 704 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (535 535 (:TYPE-PRESCRIPTION M-IDS))
 (397 397 (:REWRITE CHECKROUTES-CAAR))
 (246 246 (:TYPE-PRESCRIPTION LESSP))
 (162 162 (:TYPE-PRESCRIPTION NOTLESSP))
 (48 48 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(NOT-IN-CONS
 (69 69 (:REWRITE DEFAULT-CAR))
 (31 31 (:REWRITE DEFAULT-CDR))
 )
(NOT-IN-V-IDS-CT
 (3462 214 (:REWRITE NTH-WITH-LARGE-INDEX))
 (2033 107 (:DEFINITION NTH))
 (1225 1130 (:REWRITE DEFAULT-CDR))
 (1218 1218 (:TYPE-PRESCRIPTION LEN))
 (1015 203 (:DEFINITION LEN))
 (1002 86 (:DEFINITION NO_INTERSECTP))
 (870 109 (:DEFINITION MEMBER-EQUAL))
 (812 721 (:REWRITE DEFAULT-CAR))
 (770 77 (:REWRITE VALIDFIELD-ROUTE-TEST_PREV_ROUTES))
 (627 19 (:REWRITE NO_INTERSECTP_APPEND))
 (575 86 (:DEFINITION VALIDFIELD-ROUTE))
 (433 230 (:REWRITE DEFAULT-<-2))
 (406 203 (:REWRITE DEFAULT-+-2))
 (230 230 (:REWRITE LESSP-IMPLIES-<))
 (230 230 (:REWRITE DEFAULT-<-1))
 (221 221 (:REWRITE NOTLESSP-IMPLIES-NOT-<))
 (203 203 (:TYPE-PRESCRIPTION NFIX))
 (203 203 (:REWRITE DEFAULT-+-1))
 (203 203 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (144 18 (:REWRITE NOTLESSP-IMPLIES-NOT-<-CAR))
 (135 27 (:REWRITE LESSP-IMPLIES-<-CAR))
 (117 9 (:DEFINITION NOTLESSP))
 (99 9 (:DEFINITION LESSP))
 (86 86 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (54 54 (:TYPE-PRESCRIPTION NOTLESSP))
 (54 54 (:TYPE-PRESCRIPTION LESSP))
 (50 50 (:REWRITE CHECKROUTES-CAAR))
 (10 5 (:TYPE-PRESCRIPTION CONSP-APPEND . 2))
 (5 5 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (5 5 (:TYPE-PRESCRIPTION CONSP-APPEND . 1))
 (5 5 (:TYPE-PRESCRIPTION BINARY-APPEND))
 )
(CHECK-COMPLIANCE-CIRCUIT-SCHEDULING
 (6052 356 (:REWRITE NTH-WITH-LARGE-INDEX))
 (3600 30 (:DEFINITION CT-SCHED-NT-SCHED))
 (3396 185 (:DEFINITION NTH))
 (3280 41 (:DEFINITION CT-SCHED-NT-DEL))
 (3157 51 (:DEFINITION V-IDS))
 (2336 2241 (:REWRITE DEFAULT-CDR))
 (2136 2136 (:TYPE-PRESCRIPTION LEN))
 (1975 164 (:REWRITE NOTLESSP-IMPLIES-NOT-<-CAR))
 (1893 297 (:REWRITE LESSP-IMPLIES-<-CAR))
 (1780 356 (:DEFINITION LEN))
 (1771 381 (:DEFINITION TRUE-LISTP))
 (1729 82 (:DEFINITION NOTLESSP))
 (1640 41 (:DEFINITION UPDATE_ROUTE))
 (1463 133 (:DEFINITION LESSP))
 (1320 11 (:DEFINITION CT-SCHEDULER))
 (1312 164 (:REWRITE APPEND-TO-NIL))
 (1312 164 (:REWRITE APPEND-RIGHT-ID))
 (1296 1202 (:REWRITE DEFAULT-CAR))
 (1275 17 (:DEFINITION CONSUME-ATTEMPTS))
 (1072 693 (:REWRITE DEFAULT-<-2))
 (882 475 (:REWRITE DEFAULT-+-2))
 (798 798 (:TYPE-PRESCRIPTION LESSP))
 (693 693 (:REWRITE LESSP-IMPLIES-<))
 (693 693 (:REWRITE DEFAULT-<-1))
 (560 560 (:REWRITE NOTLESSP-IMPLIES-NOT-<))
 (526 475 (:REWRITE DEFAULT-+-1))
 (492 492 (:TYPE-PRESCRIPTION NOTLESSP))
 (396 36 (:DEFINITION MEMBER-EQUAL))
 (356 356 (:TYPE-PRESCRIPTION NFIX))
 (356 356 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (339 12 (:REWRITE MEMBER-EQUAL-M-IDS-ASSOC-EQUAL))
 (328 82 (:DEFINITION TEST_PREV_ROUTES))
 (270 6 (:DEFINITION ASSOC-EQUAL))
 (164 82 (:REWRITE COMMUTATIVITY_NO_INTERSECTP))
 (145 31 (:DEFINITION VALIDFIELD-ROUTE))
 (129 9 (:DEFINITION M-IDS))
 (82 82 (:DEFINITION NO_INTERSECTP))
 (63 63 (:TYPE-PRESCRIPTION M-IDS))
 )
(ALL_NO_INTERSECTP)
(FULLNOINTERSECTP
 (68 4 (:REWRITE NTH-WITH-LARGE-INDEX))
 (53 1 (:DEFINITION ALL_NO_INTERSECTP))
 (44 20 (:REWRITE DEFAULT-+-2))
 (42 2 (:DEFINITION INTEGER-ABS))
 (38 2 (:DEFINITION NTH))
 (27 20 (:REWRITE DEFAULT-+-1))
 (25 5 (:DEFINITION LEN))
 (20 20 (:REWRITE DEFAULT-CDR))
 (16 2 (:REWRITE NOTLESSP-IMPLIES-NOT-<-CAR))
 (15 9 (:REWRITE DEFAULT-<-2))
 (15 3 (:REWRITE LESSP-IMPLIES-<-CAR))
 (13 13 (:REWRITE DEFAULT-CAR))
 (13 1 (:DEFINITION NOTLESSP))
 (11 1 (:DEFINITION NO_INTERSECTP))
 (11 1 (:DEFINITION LESSP))
 (10 9 (:REWRITE DEFAULT-<-1))
 (9 9 (:REWRITE LESSP-IMPLIES-<))
 (8 8 (:REWRITE NOTLESSP-IMPLIES-NOT-<))
 (8 2 (:REWRITE COMMUTATIVITY-OF-+))
 (8 1 (:DEFINITION LENGTH))
 (6 6 (:TYPE-PRESCRIPTION NOTLESSP))
 (6 6 (:TYPE-PRESCRIPTION LESSP))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (4 1 (:DEFINITION MEMBER-EQUAL))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:REWRITE CHECKROUTES-CAAR))
 (2 1 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (1 1 (:TYPE-PRESCRIPTION NO_INTERSECTP))
 (1 1 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (1 1 (:REWRITE DEFAULT-REALPART))
 (1 1 (:REWRITE DEFAULT-NUMERATOR))
 (1 1 (:REWRITE DEFAULT-IMAGPART))
 (1 1 (:REWRITE DEFAULT-DENOMINATOR))
 (1 1 (:REWRITE DEFAULT-COERCE-2))
 (1 1 (:REWRITE DEFAULT-COERCE-1))
 )
(TEST_PREV_ROUTES-CHECK-NO_INTERSECTP
 (91 17 (:DEFINITION MEMBER-EQUAL))
 (50 50 (:REWRITE DEFAULT-CAR))
 (46 46 (:REWRITE DEFAULT-CDR))
 (40 4 (:REWRITE VALIDFIELD-ROUTE-TEST_PREV_ROUTES))
 (34 17 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (28 4 (:DEFINITION VALIDFIELD-ROUTE))
 (20 20 (:TYPE-PRESCRIPTION VALIDFIELD-ROUTE))
 (17 17 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(ALL_NO_INTERSECTP-APPEND
 (612 36 (:REWRITE NTH-WITH-LARGE-INDEX))
 (342 18 (:DEFINITION NTH))
 (180 36 (:DEFINITION LEN))
 (130 130 (:REWRITE DEFAULT-CDR))
 (101 101 (:REWRITE DEFAULT-CAR))
 (84 28 (:DEFINITION MEMBER-EQUAL))
 (72 36 (:REWRITE DEFAULT-<-2))
 (72 36 (:REWRITE DEFAULT-+-2))
 (56 28 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (36 36 (:REWRITE NOTLESSP-IMPLIES-NOT-<))
 (36 36 (:REWRITE LESSP-IMPLIES-<))
 (36 36 (:REWRITE DEFAULT-<-1))
 (36 36 (:REWRITE DEFAULT-+-1))
 (36 36 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (28 28 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (27 9 (:DEFINITION BINARY-APPEND))
 )
(FULLNOINTERSECTP-ALL_NO_INTERSECTP
 (3468 201 (:REWRITE NTH-WITH-LARGE-INDEX))
 (1767 93 (:DEFINITION NTH))
 (1715 207 (:DEFINITION LEN))
 (1092 1092 (:TYPE-PRESCRIPTION LEN))
 (748 70 (:DEFINITION NO_INTERSECTP))
 (659 656 (:REWRITE DEFAULT-CDR))
 (384 192 (:REWRITE DEFAULT-+-2))
 (376 375 (:REWRITE DEFAULT-CAR))
 (354 177 (:REWRITE DEFAULT-<-2))
 (330 33 (:REWRITE VALIDFIELD-ROUTE-TEST_PREV_ROUTES))
 (312 24 (:DEFINITION BINARY-APPEND))
 (294 70 (:DEFINITION MEMBER-EQUAL))
 (231 33 (:DEFINITION VALIDFIELD-ROUTE))
 (231 7 (:REWRITE NO_INTERSECTP_APPEND))
 (192 192 (:TYPE-PRESCRIPTION NFIX))
 (192 192 (:REWRITE DEFAULT-+-1))
 (177 177 (:REWRITE NOTLESSP-IMPLIES-NOT-<))
 (177 177 (:REWRITE LESSP-IMPLIES-<))
 (177 177 (:REWRITE DEFAULT-<-1))
 (177 177 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (165 165 (:TYPE-PRESCRIPTION VALIDFIELD-ROUTE))
 (140 70 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (70 70 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (70 70 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (30 1 (:REWRITE NO_INTERSECTP_APPEND-1))
 (28 28 (:REWRITE CHECKROUTES-CAAR))
 )
(FULLNOINTERSECTP-CT-SCHEDULER
 (2304 137 (:REWRITE NTH-WITH-LARGE-INDEX))
 (1273 67 (:DEFINITION NTH))
 (816 136 (:DEFINITION LEN))
 (786 786 (:TYPE-PRESCRIPTION LEN))
 (638 590 (:REWRITE DEFAULT-CDR))
 (462 8 (:DEFINITION ALL_NO_INTERSECTP))
 (405 37 (:DEFINITION NO_INTERSECTP))
 (366 323 (:REWRITE DEFAULT-CAR))
 (295 50 (:DEFINITION MEMBER-EQUAL))
 (287 157 (:REWRITE DEFAULT-<-2))
 (266 133 (:REWRITE DEFAULT-+-2))
 (180 18 (:REWRITE VALIDFIELD-ROUTE-TEST_PREV_ROUTES))
 (162 27 (:DEFINITION VALIDFIELD-ROUTE))
 (157 157 (:REWRITE LESSP-IMPLIES-<))
 (157 157 (:REWRITE DEFAULT-<-1))
 (148 148 (:REWRITE NOTLESSP-IMPLIES-NOT-<))
 (144 18 (:REWRITE NOTLESSP-IMPLIES-NOT-<-CAR))
 (135 27 (:REWRITE LESSP-IMPLIES-<-CAR))
 (133 133 (:TYPE-PRESCRIPTION NFIX))
 (133 133 (:REWRITE DEFAULT-+-1))
 (132 4 (:REWRITE NO_INTERSECTP_APPEND))
 (130 130 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (117 9 (:DEFINITION NOTLESSP))
 (99 9 (:DEFINITION LESSP))
 (54 54 (:TYPE-PRESCRIPTION NOTLESSP))
 (54 54 (:TYPE-PRESCRIPTION LESSP))
 (39 39 (:REWRITE CONS-V-IDS))
 (37 37 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (34 34 (:REWRITE CHECKROUTES-CAAR))
 (30 1 (:REWRITE NO_INTERSECTP_APPEND-1))
 )
