(PREFIXP)
(SKIP-JSON-WHITESPACE)
(LEN-OF-SKIP-JSON-WHITESPACE-BOUND
 (45 45 (:REWRITE DEFAULT-CAR))
 (40 20 (:REWRITE DEFAULT-+-2))
 (22 11 (:REWRITE DEFAULT-<-2))
 (22 11 (:REWRITE DEFAULT-<-1))
 (20 20 (:TYPE-PRESCRIPTION SKIP-JSON-WHITESPACE))
 (20 20 (:REWRITE DEFAULT-+-1))
 (14 14 (:REWRITE DEFAULT-CDR))
 )
(CHARACTER-LISTP-OF-SKIP-JSON-WHITESPACE
 (108 108 (:REWRITE DEFAULT-CAR))
 (54 54 (:REWRITE DEFAULT-CDR))
 )
(LEN-OF-CDR
 (10 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE DEFAULT-+-1))
 )
(TRUE-LISTP-OF-CDR)
(LEN-OF-CDR-LINEAR
 (45 3 (:LINEAR LEN-OF-CDR))
 (36 19 (:REWRITE DEFAULT-+-2))
 (19 19 (:REWRITE DEFAULT-+-1))
 (4 2 (:REWRITE DEFAULT-<-2))
 (4 2 (:REWRITE DEFAULT-<-1))
 )
(PARSE-JSON-TRUE-LITERAL
 (2 1 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(LEN-OF-MV-NTH-2-OF-PARSE-JSON-TRUE-LITERAL
 (102 102 (:REWRITE DEFAULT-CDR))
 (58 29 (:REWRITE DEFAULT-+-2))
 (29 29 (:REWRITE DEFAULT-+-1))
 (24 24 (:REWRITE DEFAULT-CAR))
 (12 6 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (6 6 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(CHARACTER-LISTP-OF-MV-NTH-2-OF-PARSE-JSON-TRUE-LITERAL
 (64 22 (:REWRITE CHARACTER-LISTP-OF-CDR))
 (58 58 (:REWRITE DEFAULT-CDR))
 (21 21 (:REWRITE DEFAULT-CAR))
 (4 2 (:DEFINITION NTHCDR))
 )
(PARSE-JSON-FALSE-LITERAL
 (2 1 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(LEN-OF-MV-NTH-2-OF-PARSE-JSON-FALSE-LITERAL
 (148 148 (:REWRITE DEFAULT-CDR))
 (62 31 (:REWRITE DEFAULT-+-2))
 (31 31 (:REWRITE DEFAULT-+-1))
 (30 30 (:REWRITE DEFAULT-CAR))
 (12 6 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (6 6 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(CHARACTER-LISTP-OF-MV-NTH-2-OF-PARSE-JSON-FALSE-LITERAL
 (89 89 (:REWRITE DEFAULT-CDR))
 (84 30 (:REWRITE CHARACTER-LISTP-OF-CDR))
 (26 26 (:REWRITE DEFAULT-CAR))
 (4 2 (:DEFINITION NTHCDR))
 )
(PARSE-JSON-NULL-LITERAL
 (2 1 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(LEN-OF-MV-NTH-2-OF-PARSE-JSON-NULL-LITERAL
 (102 102 (:REWRITE DEFAULT-CDR))
 (58 29 (:REWRITE DEFAULT-+-2))
 (29 29 (:REWRITE DEFAULT-+-1))
 (24 24 (:REWRITE DEFAULT-CAR))
 (12 6 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (6 6 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(CHARACTER-LISTP-OF-MV-NTH-2-OF-PARSE-JSON-NULL-LITERAL
 (64 22 (:REWRITE CHARACTER-LISTP-OF-CDR))
 (58 58 (:REWRITE DEFAULT-CDR))
 (21 21 (:REWRITE DEFAULT-CAR))
 (4 2 (:DEFINITION NTHCDR))
 )
(HEX-DIGITP)
(PARSE-UNICODE-DIGITS
 (144 31 (:REWRITE CHARACTER-LISTP-OF-CDR))
 (63 63 (:REWRITE DEFAULT-CDR))
 (24 24 (:REWRITE DEFAULT-CAR))
 )
(LEN-OF-MV-NTH-2-OF-PARSE-UNICODE-DIGITS-BOUND
 (88 88 (:REWRITE DEFAULT-CDR))
 (58 29 (:REWRITE DEFAULT-+-2))
 (29 29 (:REWRITE DEFAULT-+-1))
 (16 16 (:REWRITE DEFAULT-CAR))
 (6 3 (:REWRITE DEFAULT-<-2))
 (6 3 (:REWRITE DEFAULT-<-1))
 (2 2 (:LINEAR LEN-OF-CDR))
 )
(CHARACTER-LISTP-OF-MV-NTH-2-OF-PARSE-UNICODE-DIGITS
 (15 15 (:REWRITE DEFAULT-CDR))
 (14 2 (:DEFINITION CHARACTER-LISTP))
 (8 2 (:REWRITE CHARACTER-LISTP-OF-CDR))
 (6 6 (:REWRITE DEFAULT-CAR))
 )
(CHARACTER-LISTP-OF-MV-NTH-1-OF-PARSE-UNICODE-DIGITS
 (152 33 (:REWRITE CHARACTER-LISTP-OF-CDR))
 (78 78 (:REWRITE DEFAULT-CDR))
 (34 34 (:REWRITE DEFAULT-CAR))
 )
(PARSE-JSON-STRING-CHAR
 (6 6 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE DEFAULT-CDR))
 )
(MV-NTH-2-OF-PARSE-JSON-STRING-CHAR-BOUND
 (194 97 (:REWRITE DEFAULT-+-2))
 (166 166 (:REWRITE DEFAULT-CAR))
 (121 121 (:REWRITE DEFAULT-CDR))
 (97 97 (:REWRITE DEFAULT-+-1))
 (38 19 (:REWRITE DEFAULT-<-2))
 (38 19 (:REWRITE DEFAULT-<-1))
 )
(CHARACTER-LISTP-OF-MV-NTH-2-OF-PARSE-JSON-STRING-CHAR
 (68 68 (:REWRITE DEFAULT-CAR))
 (14 2 (:DEFINITION CHARACTER-LISTP))
 (12 12 (:REWRITE DEFAULT-CDR))
 (8 2 (:REWRITE CHARACTER-LISTP-OF-CDR))
 )
(CHARACTER-LISTP-OF-MV-NTH-1-OF-PARSE-JSON-STRING-CHAR
 (104 104 (:REWRITE DEFAULT-CAR))
 (13 13 (:REWRITE DEFAULT-CDR))
 (12 3 (:REWRITE CHARACTER-LISTP-OF-CDR))
 )
(LEN-OF-MV-NTH-2-OF-PARSE-JSON-STRING-CHAR-BOUND
 (232 232 (:REWRITE DEFAULT-CAR))
 (198 99 (:REWRITE DEFAULT-+-2))
 (133 133 (:REWRITE DEFAULT-CDR))
 (99 99 (:REWRITE DEFAULT-+-1))
 (38 19 (:REWRITE DEFAULT-<-2))
 (38 19 (:REWRITE DEFAULT-<-1))
 )
(PARSE-JSON-STRING-CHARS-AND-FINAL-QUOTE
 (15 3 (:DEFINITION LEN))
 (6 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-+-1))
 (2 1 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (1 1 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(LEN-OF-MV-NTH-2-OF-PARSE-JSON-STRING-CHARS-AND-FINAL-QUOTE-BOUND
 (72 36 (:REWRITE DEFAULT-+-2))
 (56 56 (:REWRITE DEFAULT-CDR))
 (36 36 (:REWRITE DEFAULT-CAR))
 (36 36 (:REWRITE DEFAULT-+-1))
 (33 11 (:DEFINITION BINARY-APPEND))
 (22 11 (:REWRITE DEFAULT-<-1))
 (21 11 (:REWRITE DEFAULT-<-2))
 )
(CHARACTER-LISTP-OF-MV-NTH-2-OF-PARSE-JSON-STRING-CHARS-AND-FINAL-QUOTE
 (65 65 (:REWRITE DEFAULT-CAR))
 (52 52 (:REWRITE DEFAULT-CDR))
 (39 13 (:DEFINITION BINARY-APPEND))
 )
(CHARACTER-LISTP-OF-MV-NTH-1-OF-PARSE-JSON-STRING-CHARS-AND-FINAL-QUOTE
 (56 56 (:REWRITE DEFAULT-CAR))
 (44 44 (:REWRITE DEFAULT-CDR))
 (33 11 (:DEFINITION BINARY-APPEND))
 )
(PARSE-JSON-STRING)
(LEN-OF-MV-NTH-2-OF-PARSE-JSON-STRING-BOUND
 (26 13 (:REWRITE DEFAULT-+-2))
 (13 13 (:REWRITE DEFAULT-+-1))
 (4 2 (:REWRITE DEFAULT-<-2))
 (4 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE DEFAULT-COERCE-3))
 (2 2 (:REWRITE DEFAULT-COERCE-2))
 )
(CHARACTER-LISTP-OF-MV-NTH-2-OF-PARSE-JSON-STRING
 (20 5 (:REWRITE CHARACTER-LISTP-OF-CDR))
 (5 5 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-COERCE-3))
 (1 1 (:REWRITE DEFAULT-COERCE-2))
 )
(STRINGP-OF-MV-NTH-1-OF-PARSE-JSON-STRING
 (16 4 (:REWRITE CHARACTER-LISTP-OF-CDR))
 (4 4 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-COERCE-3))
 (1 1 (:REWRITE DEFAULT-COERCE-2))
 )
(CHAR-VALUE)
(PARSE-JSON-DIGITS)
(NATP-OF-EXPT
 (29 25 (:REWRITE DEFAULT-<-1))
 (25 25 (:REWRITE DEFAULT-<-2))
 (16 6 (:REWRITE DEFAULT-*-2))
 (12 12 (:REWRITE DEFAULT-+-2))
 (12 12 (:REWRITE DEFAULT-+-1))
 (6 6 (:REWRITE ZIP-OPEN))
 (6 6 (:REWRITE DEFAULT-*-1))
 )
(NATP-OF-MV-NTH-1-OF-PARSE-JSON-DIGITS
 (1730 74 (:DEFINITION EXPT))
 (1447 1447 (:REWRITE DEFAULT-CAR))
 (1324 1324 (:REWRITE DEFAULT-CDR))
 (1030 286 (:REWRITE DEFAULT-*-2))
 (996 518 (:REWRITE DEFAULT-+-2))
 (932 518 (:REWRITE DEFAULT-+-1))
 (626 286 (:REWRITE DEFAULT-*-1))
 (320 320 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (256 256 (:TYPE-PRESCRIPTION CHAR-VALUE))
 (214 214 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (138 74 (:REWRITE ZIP-OPEN))
 (130 128 (:REWRITE DEFAULT-<-1))
 (128 128 (:REWRITE DEFAULT-<-2))
 )
(NATP-OF-MV-NTH-0-OF-PARSE-JSON-DIGITS
 (1938 114 (:DEFINITION EXPT))
 (1867 1867 (:REWRITE DEFAULT-CAR))
 (1764 1764 (:REWRITE DEFAULT-CDR))
 (1134 530 (:REWRITE DEFAULT-+-2))
 (980 530 (:REWRITE DEFAULT-+-1))
 (968 320 (:REWRITE DEFAULT-*-2))
 (686 320 (:REWRITE DEFAULT-*-1))
 (342 114 (:REWRITE ZIP-OPEN))
 (336 336 (:TYPE-PRESCRIPTION CHAR-VALUE))
 (200 168 (:REWRITE DEFAULT-<-1))
 (170 170 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (168 168 (:REWRITE DEFAULT-<-2))
 )
(PARSE-JSON-DIGITS
 (28 28 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 )
(CHARACTER-LISTP-OF-MV-NTH-2-OF-PARSE-JSON-DIGITS
 (867 867 (:REWRITE DEFAULT-CAR))
 (763 763 (:REWRITE DEFAULT-CDR))
 (714 42 (:DEFINITION EXPT))
 (452 210 (:REWRITE DEFAULT-+-2))
 (410 210 (:REWRITE DEFAULT-+-1))
 (368 126 (:REWRITE DEFAULT-*-2))
 (284 126 (:REWRITE DEFAULT-*-1))
 (128 128 (:TYPE-PRESCRIPTION CHAR-VALUE))
 (126 42 (:REWRITE ZIP-OPEN))
 (84 84 (:TYPE-PRESCRIPTION NATP-OF-MV-NTH-0-OF-PARSE-JSON-DIGITS))
 (42 42 (:REWRITE DEFAULT-<-2))
 (42 42 (:REWRITE DEFAULT-<-1))
 )
(LEN-OF-MV-NTH-2-OF-PARSE-JSON-DIGITS-BOUND-WHEN-DIGIT-BOUND
 (9179 4838 (:REWRITE DEFAULT-+-2))
 (6201 4838 (:REWRITE DEFAULT-+-1))
 (5780 340 (:DEFINITION EXPT))
 (4309 101 (:LINEAR LEN-OF-CDR))
 (4004 101 (:LINEAR LEN-OF-CDR-LINEAR))
 (3116 3116 (:REWRITE DEFAULT-CDR))
 (2725 1019 (:REWRITE DEFAULT-*-2))
 (2042 1019 (:REWRITE DEFAULT-*-1))
 (1416 1416 (:REWRITE DEFAULT-CAR))
 (1094 717 (:REWRITE DEFAULT-<-1))
 (1020 340 (:REWRITE ZIP-OPEN))
 (994 717 (:REWRITE DEFAULT-<-2))
 (679 679 (:TYPE-PRESCRIPTION NATP-OF-MV-NTH-0-OF-PARSE-JSON-DIGITS))
 (24 24 (:TYPE-PRESCRIPTION CHAR-VALUE))
 )
(LEN-OF-MV-NTH-2-OF-PARSE-JSON-DIGITS-BOUND-BOUND
 (975 476 (:REWRITE DEFAULT-+-2))
 (654 654 (:REWRITE DEFAULT-CDR))
 (631 476 (:REWRITE DEFAULT-+-1))
 (566 566 (:REWRITE DEFAULT-CAR))
 (561 33 (:DEFINITION EXPT))
 (464 11 (:LINEAR LEN-OF-CDR))
 (427 11 (:LINEAR LEN-OF-CDR-LINEAR))
 (287 99 (:REWRITE DEFAULT-*-2))
 (221 99 (:REWRITE DEFAULT-*-1))
 (123 78 (:REWRITE DEFAULT-<-2))
 (122 78 (:REWRITE DEFAULT-<-1))
 (99 33 (:REWRITE ZIP-OPEN))
 (92 92 (:TYPE-PRESCRIPTION CHAR-VALUE))
 (66 66 (:TYPE-PRESCRIPTION NATP-OF-MV-NTH-0-OF-PARSE-JSON-DIGITS))
 )
(PARSE-INTEGER-PART-OF-JSON-NUMBER
 (75 75 (:REWRITE DEFAULT-CAR))
 (34 2 (:DEFINITION EXPT))
 (12 4 (:REWRITE DEFAULT-*-2))
 (8 4 (:REWRITE DEFAULT-*-1))
 (7 1 (:DEFINITION CHARACTER-LISTP))
 (6 2 (:REWRITE ZIP-OPEN))
 (6 2 (:REWRITE COMMUTATIVITY-OF-+))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (3 3 (:TYPE-PRESCRIPTION NATP))
 (3 3 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 )
(NATP-OF-MV-NTH-1-OF-PARSE-INTEGER-PART-OF-JSON-NUMBER
 (68 4 (:DEFINITION EXPT))
 (40 40 (:REWRITE DEFAULT-CAR))
 (30 14 (:REWRITE DEFAULT-+-2))
 (26 14 (:REWRITE DEFAULT-+-1))
 (24 8 (:REWRITE DEFAULT-*-2))
 (16 8 (:REWRITE DEFAULT-*-1))
 (12 4 (:REWRITE ZIP-OPEN))
 (11 6 (:REWRITE DEFAULT-<-1))
 (8 8 (:TYPE-PRESCRIPTION CHAR-VALUE))
 (8 8 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(CHARACTER-LISTP-OF-MV-NTH-2-OF-PARSE-INTEGER-PART-OF-JSON-NUMBER
 (21 21 (:REWRITE DEFAULT-CAR))
 (17 1 (:DEFINITION EXPT))
 (14 2 (:DEFINITION CHARACTER-LISTP))
 (9 5 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (9 4 (:REWRITE DEFAULT-+-2))
 (9 4 (:REWRITE DEFAULT-+-1))
 (9 3 (:REWRITE DEFAULT-*-2))
 (8 8 (:TYPE-PRESCRIPTION NATP-OF-MV-NTH-1-OF-PARSE-JSON-DIGITS))
 (8 2 (:REWRITE CHARACTER-LISTP-OF-CDR))
 (7 3 (:REWRITE DEFAULT-*-1))
 (5 5 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (4 4 (:TYPE-PRESCRIPTION CHAR-VALUE))
 (4 4 (:REWRITE DEFAULT-CDR))
 (3 1 (:REWRITE ZIP-OPEN))
 (2 2 (:TYPE-PRESCRIPTION NATP-OF-MV-NTH-0-OF-PARSE-JSON-DIGITS))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(LEN-OF-MV-NTH-2-OF-PARSE-INTEGER-PART-OF-JSON-NUMBER-BOUND
 (297 148 (:REWRITE DEFAULT-+-2))
 (189 148 (:REWRITE DEFAULT-+-1))
 (170 10 (:DEFINITION EXPT))
 (100 100 (:REWRITE DEFAULT-CDR))
 (81 30 (:REWRITE DEFAULT-*-2))
 (61 30 (:REWRITE DEFAULT-*-1))
 (50 30 (:REWRITE DEFAULT-<-2))
 (50 30 (:REWRITE DEFAULT-<-1))
 (39 39 (:REWRITE DEFAULT-CAR))
 (30 10 (:REWRITE ZIP-OPEN))
 (20 20 (:TYPE-PRESCRIPTION NATP-OF-MV-NTH-0-OF-PARSE-JSON-DIGITS))
 (4 4 (:TYPE-PRESCRIPTION CHAR-VALUE))
 )
(PARSE-ONE-OR-MORE-JSON-DIGITS)
(NATP-OF-MV-NTH-1-OF-PARSE-ONE-OR-MORE-JSON-DIGITS
 (42 42 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE DEFAULT-<-2))
 )
(NATP-OF-MV-NTH-2-OF-PARSE-ONE-OR-MORE-JSON-DIGITS
 (22 22 (:REWRITE DEFAULT-CAR))
 (7 1 (:DEFINITION CHARACTER-LISTP))
 (4 1 (:REWRITE CHARACTER-LISTP-OF-CDR))
 (3 1 (:DEFINITION NATP))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(CHARACTER-LISTP-OF-MV-NTH-3-OF-PARSE-ONE-OR-MORE-JSON-DIGITS
 (23 23 (:REWRITE DEFAULT-CAR))
 (14 2 (:DEFINITION CHARACTER-LISTP))
 (8 2 (:REWRITE CHARACTER-LISTP-OF-CDR))
 (2 2 (:REWRITE DEFAULT-CDR))
 )
(LEN-OF-MV-NTH-3-OF-PARSE-ONE-OR-MORE-JSON-DIGITS-BOUND
 (21 21 (:REWRITE DEFAULT-CAR))
 (10 2 (:DEFINITION LEN))
 (4 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 1 (:REWRITE DEFAULT-<-2))
 (2 1 (:REWRITE DEFAULT-<-1))
 )
(PARSE-FRACTIONAL-PART-OF-JSON-NUMBER
 (144 113 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (105 3 (:DEFINITION EXPT))
 (60 30 (:TYPE-PRESCRIPTION NATP-OF-MV-NTH-2-OF-PARSE-ONE-OR-MORE-JSON-DIGITS))
 (24 6 (:REWRITE DEFAULT-*-2))
 (24 3 (:REWRITE ZIP-OPEN))
 (18 6 (:REWRITE COMMUTATIVITY-OF-+))
 (17 1 (:REWRITE DEFAULT-UNARY-/))
 (12 12 (:REWRITE DEFAULT-+-2))
 (12 12 (:REWRITE DEFAULT-+-1))
 (11 11 (:TYPE-PRESCRIPTION NATP))
 (7 1 (:DEFINITION CHARACTER-LISTP))
 (6 6 (:REWRITE DEFAULT-*-1))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 )
(RATIONALP-OF-MV-NTH-1-OF-PARSE-FRACTIONAL-PART-OF-JSON-NUMBER
 (35 1 (:DEFINITION EXPT))
 (27 6 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (26 13 (:TYPE-PRESCRIPTION NATP-OF-MV-NTH-2-OF-PARSE-ONE-OR-MORE-JSON-DIGITS))
 (17 3 (:REWRITE DEFAULT-*-2))
 (17 1 (:REWRITE DEFAULT-UNARY-/))
 (8 1 (:REWRITE ZIP-OPEN))
 (7 1 (:DEFINITION CHARACTER-LISTP))
 (6 2 (:REWRITE COMMUTATIVITY-OF-+))
 (5 5 (:TYPE-PRESCRIPTION NATP))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (4 3 (:REWRITE DEFAULT-*-1))
 (4 1 (:REWRITE CHARACTER-LISTP-OF-CDR))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(CHARACTER-LISTP-OF-MV-NTH-2-OF-PARSE-FRACTIONAL-PART-OF-JSON-NUMBER
 (35 1 (:DEFINITION EXPT))
 (22 11 (:TYPE-PRESCRIPTION NATP-OF-MV-NTH-2-OF-PARSE-ONE-OR-MORE-JSON-DIGITS))
 (21 5 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (17 3 (:REWRITE DEFAULT-*-2))
 (17 1 (:REWRITE DEFAULT-UNARY-/))
 (14 2 (:DEFINITION CHARACTER-LISTP))
 (8 2 (:REWRITE CHARACTER-LISTP-OF-CDR))
 (8 1 (:REWRITE ZIP-OPEN))
 (6 2 (:REWRITE COMMUTATIVITY-OF-+))
 (5 5 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (4 4 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (4 4 (:TYPE-PRESCRIPTION NATP))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (4 3 (:REWRITE DEFAULT-*-1))
 (3 3 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-CAR))
 (1 1 (:TYPE-PRESCRIPTION NATP-OF-MV-NTH-1-OF-PARSE-ONE-OR-MORE-JSON-DIGITS))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(LEN-OF-MV-NTH-2-OF-PARSE-FRACTIONAL-PART-OF-JSON-NUMBER-BOUND
 (35 1 (:DEFINITION EXPT))
 (22 11 (:TYPE-PRESCRIPTION NATP-OF-MV-NTH-2-OF-PARSE-ONE-OR-MORE-JSON-DIGITS))
 (21 5 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (18 11 (:REWRITE DEFAULT-+-2))
 (17 3 (:REWRITE DEFAULT-*-2))
 (17 1 (:REWRITE DEFAULT-UNARY-/))
 (11 11 (:TYPE-PRESCRIPTION CHARACTER-LISTP))
 (11 11 (:REWRITE DEFAULT-+-1))
 (8 1 (:REWRITE ZIP-OPEN))
 (6 6 (:REWRITE DEFAULT-CDR))
 (6 2 (:REWRITE COMMUTATIVITY-OF-+))
 (5 5 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (4 4 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (4 4 (:TYPE-PRESCRIPTION NATP))
 (4 3 (:REWRITE DEFAULT-*-1))
 (3 2 (:REWRITE DEFAULT-<-2))
 (3 2 (:REWRITE DEFAULT-<-1))
 (1 1 (:TYPE-PRESCRIPTION NATP-OF-MV-NTH-1-OF-PARSE-ONE-OR-MORE-JSON-DIGITS))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(PARSE-EXPONENT-PART-OF-JSON-NUMBER
 (27 27 (:REWRITE DEFAULT-CAR))
 (20 20 (:REWRITE DEFAULT-CDR))
 (7 1 (:DEFINITION CHARACTER-LISTP))
 )
(INTEGERP-OF-MV-NTH-1-OF-PARSE-EXPONENT-PART-OF-JSON-NUMBER
 (10 10 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE DEFAULT-CDR))
 (4 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 )
(CHARACTER-LISTP-OF-MV-NTH-2-OF-PARSE-EXPONENT-PART-OF-JSON-NUMBER
 (14 2 (:DEFINITION CHARACTER-LISTP))
 (12 12 (:REWRITE DEFAULT-CAR))
 (8 8 (:REWRITE DEFAULT-CDR))
 (8 2 (:REWRITE CHARACTER-LISTP-OF-CDR))
 (4 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 )
(LEN-OF-MV-NTH-2-OF-PARSE-EXPONENT-PART-OF-JSON-NUMBER-BOUND
 (80 40 (:REWRITE DEFAULT-+-2))
 (40 40 (:REWRITE DEFAULT-+-1))
 (38 38 (:REWRITE DEFAULT-CDR))
 (10 10 (:REWRITE DEFAULT-CAR))
 (4 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 (2 1 (:REWRITE DEFAULT-<-2))
 (2 1 (:REWRITE DEFAULT-<-1))
 )
(PARSE-NON-NEGATIVE-JSON-NUMBER
 (18 16 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 )
(RATIONALP-OF-MV-NTH-1-OF-PARSE-NON-NEGATIVE-JSON-NUMBER
 (35 8 (:REWRITE DEFAULT-*-2))
 (29 8 (:REWRITE DEFAULT-*-1))
 (28 1 (:DEFINITION EXPT))
 (15 6 (:REWRITE DEFAULT-+-2))
 (13 6 (:REWRITE DEFAULT-+-1))
 (12 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (9 3 (:REWRITE RATIONALP-OF-MV-NTH-1-OF-PARSE-FRACTIONAL-PART-OF-JSON-NUMBER))
 (7 1 (:DEFINITION CHARACTER-LISTP))
 (6 2 (:REWRITE COMMUTATIVITY-OF-+))
 (4 1 (:REWRITE CHARACTER-LISTP-OF-CDR))
 (3 3 (:REWRITE CHARACTER-LISTP-OF-MV-NTH-2-OF-PARSE-INTEGER-PART-OF-JSON-NUMBER))
 (3 1 (:REWRITE ZIP-OPEN))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(CHARACTER-LISTP-OF-MV-NTH-2-OF-PARSE-NON-NEGATIVE-JSON-NUMBER
 (35 8 (:REWRITE DEFAULT-*-2))
 (29 8 (:REWRITE DEFAULT-*-1))
 (28 1 (:DEFINITION EXPT))
 (27 10 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (15 6 (:REWRITE DEFAULT-+-2))
 (14 2 (:DEFINITION CHARACTER-LISTP))
 (13 6 (:REWRITE DEFAULT-+-1))
 (12 12 (:TYPE-PRESCRIPTION INTEGERP-OF-MV-NTH-1-OF-PARSE-EXPONENT-PART-OF-JSON-NUMBER))
 (12 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (10 10 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (9 9 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (9 9 (:TYPE-PRESCRIPTION NATP))
 (9 3 (:REWRITE RATIONALP-OF-MV-NTH-1-OF-PARSE-FRACTIONAL-PART-OF-JSON-NUMBER))
 (8 2 (:REWRITE CHARACTER-LISTP-OF-CDR))
 (6 6 (:TYPE-PRESCRIPTION NATP-OF-MV-NTH-1-OF-PARSE-INTEGER-PART-OF-JSON-NUMBER))
 (6 2 (:REWRITE COMMUTATIVITY-OF-+))
 (3 3 (:REWRITE CHARACTER-LISTP-OF-MV-NTH-2-OF-PARSE-INTEGER-PART-OF-JSON-NUMBER))
 (3 1 (:REWRITE ZIP-OPEN))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(LEN-OF-MV-NTH-2-OF-PARSE-NON-NEGATIVE-JSON-NUMBER-BOUND
 (88 22 (:REWRITE DEFAULT-+-2))
 (64 16 (:REWRITE DEFAULT-*-2))
 (56 2 (:DEFINITION EXPT))
 (54 20 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (52 16 (:REWRITE DEFAULT-*-1))
 (50 10 (:DEFINITION LEN))
 (50 6 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (44 2 (:REWRITE RATIONALP-OF-MV-NTH-1-OF-PARSE-FRACTIONAL-PART-OF-JSON-NUMBER))
 (36 22 (:REWRITE DEFAULT-+-1))
 (32 4 (:DEFINITION CHARACTER-LISTP))
 (24 24 (:TYPE-PRESCRIPTION INTEGERP-OF-MV-NTH-1-OF-PARSE-EXPONENT-PART-OF-JSON-NUMBER))
 (24 24 (:TYPE-PRESCRIPTION CHARACTER-LISTP))
 (22 2 (:REWRITE CHARACTER-LISTP-OF-MV-NTH-2-OF-PARSE-INTEGER-PART-OF-JSON-NUMBER))
 (20 20 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (18 18 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (18 18 (:TYPE-PRESCRIPTION NATP))
 (14 14 (:REWRITE DEFAULT-CDR))
 (12 12 (:TYPE-PRESCRIPTION NATP-OF-MV-NTH-1-OF-PARSE-INTEGER-PART-OF-JSON-NUMBER))
 (12 4 (:REWRITE COMMUTATIVITY-OF-+))
 (8 4 (:REWRITE CHARACTER-LISTP-OF-CDR))
 (6 4 (:REWRITE DEFAULT-<-2))
 (6 4 (:REWRITE DEFAULT-<-1))
 (6 2 (:REWRITE ZIP-OPEN))
 (4 4 (:REWRITE DEFAULT-CAR))
 )
(PARSE-JSON-NUMBER)
(RATIONALP-OF-MV-NTH-1-OF-PARSE-JSON-NUMBER
 (7 1 (:DEFINITION CHARACTER-LISTP))
 (5 2 (:REWRITE CHARACTER-LISTP-OF-CDR))
 (5 1 (:REWRITE DEFAULT-*-2))
 (4 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 1 (:REWRITE RATIONALP-OF-MV-NTH-1-OF-PARSE-NON-NEGATIVE-JSON-NUMBER))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-*-1))
 )
(LEN-OF-MV-NTH-2-OF-PARSE-JSON-NUMBER-BOUND
 (48 2 (:REWRITE DEFAULT-*-2))
 (46 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (44 2 (:REWRITE RATIONALP-OF-MV-NTH-1-OF-PARSE-NON-NEGATIVE-JSON-NUMBER))
 (32 4 (:DEFINITION CHARACTER-LISTP))
 (26 13 (:REWRITE DEFAULT-+-2))
 (26 6 (:REWRITE CHARACTER-LISTP-OF-CDR))
 (24 24 (:TYPE-PRESCRIPTION CHARACTER-LISTP))
 (18 18 (:REWRITE DEFAULT-CDR))
 (13 13 (:REWRITE DEFAULT-+-1))
 (8 8 (:REWRITE DEFAULT-CAR))
 (4 2 (:REWRITE DEFAULT-<-2))
 (4 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE DEFAULT-*-1))
 )
(CHARACTER-LISTP-OF-MV-NTH-2-OF-PARSE-JSON-NUMBER
 (14 2 (:DEFINITION CHARACTER-LISTP))
 (9 3 (:REWRITE CHARACTER-LISTP-OF-CDR))
 (5 1 (:REWRITE DEFAULT-*-2))
 (4 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 3 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-CAR))
 (3 1 (:REWRITE RATIONALP-OF-MV-NTH-1-OF-PARSE-NON-NEGATIVE-JSON-NUMBER))
 (1 1 (:REWRITE DEFAULT-*-1))
 )
(TOKENIZE-JSON-CHARS-AUX
 (337 337 (:REWRITE DEFAULT-CAR))
 (271 136 (:REWRITE DEFAULT-+-2))
 (139 139 (:REWRITE DEFAULT-CDR))
 (136 136 (:REWRITE DEFAULT-+-1))
 (60 28 (:REWRITE DEFAULT-<-2))
 (58 28 (:REWRITE DEFAULT-<-1))
 (39 5 (:DEFINITION CHARACTER-LISTP))
 (39 1 (:DEFINITION TRUE-LISTP))
 (37 1 (:DEFINITION TAKE))
 (20 1 (:REWRITE ZP-OPEN))
 (15 1 (:REWRITE TRUE-LISTP-OF-CDR))
 )
(TRUE-LISTP-OF-MV-NTH-1-OF-TOKENIZE-JSON-CHARS-AUX
 (4224 288 (:REWRITE TRUE-LISTP-WHEN-CHARACTER-LISTP2))
 (3744 96 (:DEFINITION TRUE-LISTP))
 (3072 384 (:DEFINITION CHARACTER-LISTP))
 (2304 2304 (:TYPE-PRESCRIPTION CHARACTER-LISTP))
 (1632 480 (:REWRITE CHARACTER-LISTP-OF-CDR))
 (1440 96 (:REWRITE TRUE-LISTP-OF-CDR))
 (611 611 (:REWRITE DEFAULT-CAR))
 (502 502 (:REWRITE DEFAULT-CDR))
 (111 3 (:DEFINITION TAKE))
 (60 3 (:REWRITE ZP-OPEN))
 (21 6 (:REWRITE DEFAULT-<-2))
 (15 3 (:DEFINITION LEN))
 (12 4 (:DEFINITION REVAPPEND))
 (12 3 (:REWRITE DEFAULT-COERCE-3))
 (9 9 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
 (9 6 (:REWRITE DEFAULT-+-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE DEFAULT-+-1))
 (3 3 (:REWRITE DEFAULT-COERCE-2))
 )
(TOKENIZE-JSON-CHARS)
(TRUE-LISTP-OF-MV-NTH-1-OF-TOKENIZE-JSON-CHARS)
(NOT-O<-SELF
 (30 30 (:REWRITE DEFAULT-CAR))
 (18 18 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (8 4 (:REWRITE DEFAULT-<-2))
 (8 4 (:REWRITE DEFAULT-<-1))
 )
(NOT-<-SELF)
(O<-OF-MAKE-ORD-AND-MAKE-ORD-SAME-FE-AND-RST
 (8 8 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 2 (:REWRITE DEFAULT-<-2))
 (4 2 (:REWRITE DEFAULT-<-1))
 )
(O<-OF-MAKE-ORD-AND-MAKE-ORD-SAME-FE
 (32 32 (:REWRITE DEFAULT-CAR))
 (18 18 (:REWRITE DEFAULT-CDR))
 (14 14 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (14 7 (:REWRITE DEFAULT-<-2))
 (14 7 (:REWRITE DEFAULT-<-1))
 )
(O-P-OF-MAKE-ORD-SUFF
 (8 8 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE DEFAULT-CDR))
 )
(PARSE-JSON-OBJECT-PAIRS
 (180 92 (:REWRITE DEFAULT-+-2))
 (94 2 (:LINEAR LEN-OF-CDR))
 (92 92 (:REWRITE DEFAULT-+-1))
 (90 90 (:REWRITE DEFAULT-CDR))
 (88 2 (:LINEAR LEN-OF-CDR-LINEAR))
 (14 14 (:REWRITE DEFAULT-CAR))
 (14 7 (:REWRITE DEFAULT-<-1))
 (12 7 (:REWRITE DEFAULT-<-2))
 )
(FLAG-PARSE-JSON-OBJECT-PAIRS
 (164 86 (:REWRITE DEFAULT-+-2))
 (97 91 (:REWRITE DEFAULT-CDR))
 (86 86 (:REWRITE DEFAULT-+-1))
 (83 1 (:DEFINITION O-P))
 (51 51 (:TYPE-PRESCRIPTION MAKE-ORD))
 (45 30 (:REWRITE DEFAULT-CAR))
 (43 4 (:DEFINITION O-FIRST-EXPT))
 (27 6 (:DEFINITION O-FINP))
 (23 12 (:REWRITE DEFAULT-<-1))
 (19 12 (:REWRITE DEFAULT-<-2))
 (10 2 (:DEFINITION O-RST))
 (10 1 (:DEFINITION O-FIRST-COEFF))
 (3 1 (:DEFINITION POSP))
 )
(FLAG::FLAG-EQUIV-LEMMA)
(FLAG-PARSE-JSON-OBJECT-PAIRS-EQUIVALENCES)
(FLAG-LEMMA-FOR-TRUE-LIST-OF-MV-NTH-2-PARSE-JSON-OBJECT-PAIRS
 (4973 483 (:REWRITE TRUE-LISTP-WHEN-CHARACTER-LISTP2))
 (3291 564 (:DEFINITION CHARACTER-LISTP))
 (2442 255 (:REWRITE TRUE-LISTP-OF-CDR))
 (2349 2349 (:TYPE-PRESCRIPTION CHARACTER-LISTP))
 (2099 655 (:REWRITE CHARACTER-LISTP-OF-CDR))
 (1950 1950 (:REWRITE DEFAULT-CDR))
 (957 957 (:REWRITE DEFAULT-CAR))
 (314 164 (:REWRITE DEFAULT-+-2))
 (164 164 (:REWRITE DEFAULT-+-1))
 (80 44 (:REWRITE DEFAULT-<-1))
 (74 44 (:REWRITE DEFAULT-<-2))
 (14 2 (:REWRITE DEFAULT-COERCE-3))
 (6 6 (:TYPE-PRESCRIPTION TRUE-LISTP-REVAPPEND-TYPE-PRESCRIPTION))
 (6 6 (:TYPE-PRESCRIPTION REVAPPEND))
 (4 4 (:REWRITE DEFAULT-COERCE-2))
 (2 2 (:REWRITE DEFAULT-COERCE-1))
 )
(TRUE-LIST-OF-MV-NTH-2-PARSE-JSON-OBJECT-PAIRS)
(TRUE-LIST-OF-MV-NTH-2-PARSE-JSON-ARRAY-VALUES)
(TRUE-LIST-OF-MV-NTH-2-PARSE-JSON-VALUE)
(FLAG-LEMMA-FOR-LEN-OF-MV-NTH-2-PARSE-JSON-OBJECT-PAIRS-BOUND
 (1917 1917 (:REWRITE DEFAULT-CDR))
 (1206 682 (:REWRITE DEFAULT-+-2))
 (682 682 (:REWRITE DEFAULT-+-1))
 (588 12 (:LINEAR LEN-OF-CDR))
 (550 12 (:LINEAR LEN-OF-CDR-LINEAR))
 (440 440 (:REWRITE DEFAULT-CAR))
 (202 112 (:REWRITE DEFAULT-<-2))
 (176 112 (:REWRITE DEFAULT-<-1))
 (14 2 (:REWRITE DEFAULT-COERCE-3))
 (6 6 (:TYPE-PRESCRIPTION TRUE-LISTP-REVAPPEND-TYPE-PRESCRIPTION))
 (6 6 (:TYPE-PRESCRIPTION REVAPPEND))
 (4 4 (:REWRITE DEFAULT-COERCE-2))
 (2 2 (:REWRITE DEFAULT-COERCE-1))
 )
(LEN-OF-MV-NTH-2-PARSE-JSON-OBJECT-PAIRS-BOUND)
(LEN-OF-MV-NTH-2-PARSE-JSON-ARRAY-VALUES-BOUND)
(LEN-OF-MV-NTH-2-PARSE-JSON-VALUE-BOUND)
(LEN-OF-MV-NTH-2-PARSE-JSON-VALUE-BOUND-STRONG
 (86 43 (:REWRITE DEFAULT-+-2))
 (50 50 (:REWRITE DEFAULT-CDR))
 (43 43 (:REWRITE DEFAULT-+-1))
 (16 8 (:REWRITE DEFAULT-<-2))
 (16 8 (:REWRITE DEFAULT-<-1))
 (10 10 (:REWRITE DEFAULT-CAR))
 )
(PARSE-JSON-OBJECT-PAIRS
 (156 12 (:REWRITE TRUE-LISTP-WHEN-CHARACTER-LISTP2))
 (136 4 (:DEFINITION TRUE-LISTP))
 (112 14 (:DEFINITION CHARACTER-LISTP))
 (84 84 (:TYPE-PRESCRIPTION CHARACTER-LISTP))
 (64 18 (:REWRITE CHARACTER-LISTP-OF-CDR))
 (59 59 (:REWRITE DEFAULT-CDR))
 (28 28 (:REWRITE DEFAULT-CAR))
 (28 14 (:REWRITE DEFAULT-+-2))
 (14 14 (:REWRITE DEFAULT-+-1))
 (6 3 (:REWRITE DEFAULT-<-2))
 (6 3 (:REWRITE DEFAULT-<-1))
 )
(PARSE-JSON)
