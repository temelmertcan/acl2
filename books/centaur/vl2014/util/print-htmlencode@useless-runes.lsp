(VL2014::REPEATED-REVAPPEND
 (6 6 (:TYPE-PRESCRIPTION REVAPPEND-WITHOUT-GUARD))
 (5 5 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(VL2014::CHARACTER-LISTP-OF-REPEATED-REVAPPEND
 (1013 170 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (889 28 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (574 85 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (391 299 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (300 8 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (291 28 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (245 107 (:REWRITE VL2014::MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-UNDER-IFF))
 (216 2 (:REWRITE SUBSETP-APPEND1))
 (174 32 (:REWRITE SUBSETP-TRANS2))
 (170 170 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (152 3 (:REWRITE APPEND-UNDER-IFF))
 (148 8 (:REWRITE REV-WHEN-NOT-CONSP))
 (147 14 (:REWRITE REV-UNDER-IFF))
 (129 107 (:REWRITE SUBSETP-MEMBER . 2))
 (107 107 (:REWRITE SUBSETP-MEMBER . 1))
 (107 107 (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP))
 (96 12 (:REWRITE CHARACTER-LISTP-WHEN-NOT-CONSP))
 (76 17 (:REWRITE STR::CHARACTER-LISTP-WHEN-DEC-DIGIT-CHAR-LISTP))
 (53 9 (:REWRITE ZP-WHEN-INTEGERP))
 (48 9 (:REWRITE ZP-WHEN-GT-0))
 (36 36 (:TYPE-PRESCRIPTION STR::DEC-DIGIT-CHAR-LISTP))
 (32 32 (:REWRITE SUBSETP-TRANS))
 (32 8 (:REWRITE VL2014::|(< c2 (+ c1 a))|))
 (27 27 (:REWRITE CONSP-BY-LEN))
 (24 24 (:REWRITE MEMBER-SELF))
 (18 18 (:REWRITE STR::DEC-DIGIT-CHAR-LISTP-WHEN-NOT-CONSP))
 (16 16 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (13 13 (:REWRITE DEFAULT-<-2))
 (13 13 (:REWRITE DEFAULT-<-1))
 (13 13 (:META CANCEL_PLUS-LESSP-CORRECT))
 (12 4 (:REWRITE FOLD-CONSTS-IN-+))
 (10 10 (:REWRITE INTEGERP-WHEN-MEMBER-EQUAL-OF-INTEGER-LISTP))
 (10 5 (:REWRITE VL2014::INTEGERP-WHEN-NATP))
 (8 2 (:REWRITE STR::DEC-DIGIT-CHAR-LISTP-OF-REV))
 (8 1 (:REWRITE STR::DEC-DIGIT-CHAR-LISTP-OF-APPEND))
 (7 7 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE DEFAULT-+-1))
 (5 5 (:TYPE-PRESCRIPTION NATP))
 (5 5 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE LIST-FIX-UNDER-LIST-EQUIV))
 )
(VL2014::REPEATED-REVAPPEND-OF-NFIX-N
 (38 4 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (26 6 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (18 4 (:REWRITE REV-WHEN-NOT-CONSP))
 (16 2 (:REWRITE REV-UNDER-IFF))
 (12 12 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (12 12 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (10 2 (:REWRITE ZP-WHEN-INTEGERP))
 (8 8 (:TYPE-PRESCRIPTION REV))
 (8 2 (:REWRITE ZP-WHEN-GT-0))
 (4 4 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (4 4 (:REWRITE INTEGERP-WHEN-MEMBER-EQUAL-OF-INTEGER-LISTP))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE CONSP-BY-LEN))
 (4 2 (:REWRITE VL2014::INTEGERP-WHEN-NATP))
 (3 2 (:REWRITE NFIX-WHEN-NOT-NATP))
 (2 2 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:META CANCEL_PLUS-LESSP-CORRECT))
 )
(VL2014::REPEATED-REVAPPEND-NAT-EQUIV-CONGRUENCE-ON-N)
(VL2014::VL-DISTANCE-TO-TAB$INLINE
 (380 109 (:REWRITE VL2014::INTEGERP-WHEN-NATP))
 (367 367 (:REWRITE DEFAULT-*-2))
 (367 367 (:REWRITE DEFAULT-*-1))
 (338 130 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
 (298 298 (:TYPE-PRESCRIPTION MOD-TYPE . 3))
 (298 298 (:TYPE-PRESCRIPTION MOD-TYPE . 2))
 (298 298 (:TYPE-PRESCRIPTION MOD-TYPE . 1))
 (228 10 (:LINEAR MOD-TYPE . 2))
 (218 218 (:REWRITE INTEGERP-WHEN-MEMBER-EQUAL-OF-INTEGER-LISTP))
 (192 14 (:REWRITE REM-=-0 . 2))
 (180 180 (:META CANCEL_PLUS-LESSP-CORRECT))
 (166 166 (:REWRITE DEFAULT-<-2))
 (166 166 (:REWRITE DEFAULT-<-1))
 (152 141 (:REWRITE DEFAULT-+-2))
 (144 144 (:TYPE-PRESCRIPTION REM-TYPE . 3))
 (144 144 (:TYPE-PRESCRIPTION REM-TYPE . 2))
 (144 144 (:TYPE-PRESCRIPTION REM-TYPE . 1))
 (144 97 (:REWRITE SET::DOUBLE-CONTAINMENT))
 (141 141 (:REWRITE DEFAULT-+-1))
 (113 14 (:REWRITE REM-X-Y-=-X . 2))
 (97 97 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (89 32 (:REWRITE MOD-X-Y-=-X-FOR-RATIONALS . 3))
 (77 32 (:REWRITE MOD-X-Y-=-X+Y-FOR-RATIONALS . 2))
 (65 65 (:REWRITE DEFAULT-UNARY-/))
 (59 9 (:REWRITE NATP-WHEN-INTEGERP))
 (57 6 (:REWRITE VL2014::NATP-WHEN-POSP))
 (52 52 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (43 11 (:REWRITE ZP-WHEN-INTEGERP))
 (42 2 (:REWRITE NFIX-WHEN-NOT-NATP))
 (36 6 (:REWRITE NATP-RW))
 (34 7 (:REWRITE DEFAULT-UNARY-MINUS))
 (33 6 (:REWRITE VL2014::INTEGERP-OF-PLUS))
 (32 32 (:REWRITE MOD-X-Y-=-X+Y-FOR-RATIONALS . 3))
 (28 28 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (27 23 (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
 (26 26 (:REWRITE FOLD-CONSTS-IN-*))
 (16 4 (:LINEAR REM-TYPE . 3))
 (16 4 (:LINEAR REM-TYPE . 2))
 (12 12 (:REWRITE NATP-WHEN-MEMBER-EQUAL-OF-NAT-LISTP))
 (12 3 (:LINEAR X*Y>1-POSITIVE))
 (11 11 (:REWRITE ZP-OPEN))
 (10 10 (:LINEAR MOD-TYPE . 3))
 (10 10 (:LINEAR MOD-TYPE . 1))
 (6 6 (:REWRITE REDUCE-INTEGERP-+-CONSTANT))
 (4 4 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (4 4 (:REWRITE VL2014::|(< c2 (+ c1 a))|))
 (4 4 (:LINEAR REM-TYPE . 1))
 (4 2 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (4 1 (:REWRITE MOD-X-Y-=-X-FOR-RATIONALS . 1))
 (4 1 (:REWRITE MOD-=-0 . 1))
 (4 1 (:DEFINITION ZEROP))
 (3 3 (:TYPE-PRESCRIPTION TRUNCATE-TYPE . 4))
 (3 3 (:TYPE-PRESCRIPTION TRUNCATE-TYPE . 2))
 (3 3 (:TYPE-PRESCRIPTION TRUNCATE-TYPE . 1))
 (2 2 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (2 2 (:REWRITE SET::IN-SET))
 )
(VL2014::NATP-OF-VL-DISTANCE-TO-TAB)
(VL2014::VL-DISTANCE-TO-TAB$INLINE-OF-NFIX-COL)
(VL2014::VL-DISTANCE-TO-TAB$INLINE-NAT-EQUIV-CONGRUENCE-ON-COL)
(VL2014::VL-DISTANCE-TO-TAB$INLINE-OF-POS-FIX-TABSIZE)
(VL2014::VL-DISTANCE-TO-TAB$INLINE-POS-EQUIV-CONGRUENCE-ON-TABSIZE)
(VL2014::VL-HTML-ENCODE-NEXT-COL$INLINE
 (19 2 (:REWRITE VL2014::NATP-WHEN-POSP))
 (15 4 (:REWRITE VL2014::INTEGERP-WHEN-NATP))
 (12 2 (:REWRITE NATP-RW))
 (11 3 (:REWRITE ZP-WHEN-INTEGERP))
 (9 3 (:REWRITE ZP-WHEN-GT-0))
 (8 8 (:REWRITE INTEGERP-WHEN-MEMBER-EQUAL-OF-INTEGER-LISTP))
 (7 2 (:REWRITE NATP-WHEN-GTE-0))
 (6 6 (:REWRITE SET::DOUBLE-CONTAINMENT))
 (6 6 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (6 6 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (6 2 (:REWRITE NATP-WHEN-INTEGERP))
 (4 4 (:REWRITE NATP-WHEN-MEMBER-EQUAL-OF-NAT-LISTP))
 (3 3 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (3 3 (:META CANCEL_PLUS-LESSP-CORRECT))
 (2 2 (:REWRITE CHARACTERP-WHEN-MEMBER-EQUAL-OF-CHARACTER-LISTP))
 (2 1 (:REWRITE VL2014::NEGATIVE-WHEN-NATP))
 (1 1 (:TYPE-PRESCRIPTION ZP))
 (1 1 (:REWRITE NFIX-WHEN-NOT-NATP))
 )
(VL2014::NATP-OF-VL-HTML-ENCODE-NEXT-COL)
(VL2014::VL-HTML-ENCODE-NEXT-COL$INLINE-OF-CHAR-FIX-CHAR1)
(VL2014::VL-HTML-ENCODE-NEXT-COL$INLINE-CHAREQV-CONGRUENCE-ON-CHAR1)
(VL2014::VL-HTML-ENCODE-NEXT-COL$INLINE-OF-NFIX-COL)
(VL2014::VL-HTML-ENCODE-NEXT-COL$INLINE-NAT-EQUIV-CONGRUENCE-ON-COL)
(VL2014::VL-HTML-ENCODE-NEXT-COL$INLINE-OF-POS-FIX-TABSIZE
 (40 2 (:REWRITE NFIX-WHEN-NATP))
 (32 2 (:REWRITE POSP-REDEFINITION))
 (20 2 (:REWRITE VL2014::NATP-WHEN-POSP))
 (18 1 (:REWRITE POS-FIX-WHEN-POSP))
 (12 4 (:REWRITE ZP-WHEN-INTEGERP))
 (11 2 (:REWRITE NFIX-WHEN-NOT-NATP))
 (10 4 (:REWRITE ZP-WHEN-GT-0))
 (10 2 (:DEFINITION NOT))
 (9 9 (:TYPE-PRESCRIPTION NATP))
 (8 8 (:REWRITE INTEGERP-WHEN-MEMBER-EQUAL-OF-INTEGER-LISTP))
 (8 4 (:REWRITE VL2014::INTEGERP-WHEN-NATP))
 (8 4 (:REWRITE SET::DOUBLE-CONTAINMENT))
 (8 4 (:REWRITE DEFAULT-+-2))
 (7 2 (:REWRITE NATP-WHEN-GTE-0))
 (6 4 (:REWRITE DEFAULT-+-1))
 (6 2 (:REWRITE NATP-WHEN-INTEGERP))
 (6 2 (:REWRITE NATP-RW))
 (4 4 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE NATP-WHEN-MEMBER-EQUAL-OF-NAT-LISTP))
 (4 4 (:REWRITE CHARACTERP-WHEN-MEMBER-EQUAL-OF-CHARACTER-LISTP))
 (4 4 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (4 4 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (4 2 (:REWRITE CHAR-FIX-WHEN-CHARACTERP))
 (4 2 (:REWRITE CHAR-FIX-DEFAULT))
 (3 3 (:TYPE-PRESCRIPTION POSP))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (3 3 (:META CANCEL_PLUS-LESSP-CORRECT))
 (2 2 (:TYPE-PRESCRIPTION ZP))
 (2 1 (:REWRITE VL2014::NEGATIVE-WHEN-NATP))
 )
(VL2014::VL-HTML-ENCODE-NEXT-COL$INLINE-POS-EQUIV-CONGRUENCE-ON-TABSIZE)
(VL2014::VL-HTML-ENCODE-PUSH
 (83 83 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (80 40 (:TYPE-PRESCRIPTION TRUE-LISTP-REVAPPEND-TYPE-PRESCRIPTION))
 (80 40 (:TYPE-PRESCRIPTION TRUE-LISTP-REVAPPEND))
 (19 2 (:REWRITE VL2014::NATP-WHEN-POSP))
 (18 8 (:REWRITE SET::DOUBLE-CONTAINMENT))
 (15 4 (:REWRITE VL2014::INTEGERP-WHEN-NATP))
 (12 2 (:REWRITE NATP-RW))
 (11 3 (:REWRITE ZP-WHEN-INTEGERP))
 (9 3 (:REWRITE ZP-WHEN-GT-0))
 (8 8 (:REWRITE INTEGERP-WHEN-MEMBER-EQUAL-OF-INTEGER-LISTP))
 (8 8 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (8 8 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (7 2 (:REWRITE NATP-WHEN-GTE-0))
 (6 6 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (6 6 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (6 3 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (6 2 (:REWRITE NATP-WHEN-INTEGERP))
 (4 4 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (4 4 (:REWRITE NATP-WHEN-MEMBER-EQUAL-OF-NAT-LISTP))
 (4 2 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (3 3 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE CONSP-BY-LEN))
 (3 3 (:META CANCEL_PLUS-LESSP-CORRECT))
 (2 2 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (2 2 (:REWRITE SET::IN-SET))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE CHARACTERP-WHEN-MEMBER-EQUAL-OF-CHARACTER-LISTP))
 (2 2 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (2 1 (:REWRITE VL2014::NEGATIVE-WHEN-NATP))
 (1 1 (:TYPE-PRESCRIPTION ZP))
 (1 1 (:REWRITE NFIX-WHEN-NOT-NATP))
 )
(VL2014::CHARACTER-LISTP-OF-VL-HTML-ENCODE-PUSH
 (1901 121 (:REWRITE SUBSETP-OF-CONS))
 (897 231 (:REWRITE VL2014::MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-UNDER-IFF))
 (637 610 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (251 59 (:REWRITE STR::CHARACTER-LISTP-WHEN-DEC-DIGIT-CHAR-LISTP))
 (231 231 (:REWRITE SUBSETP-MEMBER . 2))
 (231 231 (:REWRITE SUBSETP-MEMBER . 1))
 (231 231 (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP))
 (187 68 (:REWRITE CHARACTERP-WHEN-MEMBER-EQUAL-OF-CHARACTER-LISTP))
 (170 170 (:REWRITE SUBSETP-TRANS2))
 (170 170 (:REWRITE SUBSETP-TRANS))
 (170 17 (:REWRITE CHAR-FIX-WHEN-CHARACTERP))
 (155 50 (:REWRITE CHARACTER-LISTP-WHEN-NOT-CONSP))
 (91 91 (:REWRITE DEFAULT-CDR))
 (80 80 (:TYPE-PRESCRIPTION STR::DEC-DIGIT-CHAR-LISTP))
 (80 28 (:REWRITE SET::DOUBLE-CONTAINMENT))
 (67 60 (:REWRITE STR::DEC-DIGIT-CHAR-LISTP-WHEN-NOT-CONSP))
 (64 1 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (63 28 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (51 17 (:REWRITE CHAR-FIX-DEFAULT))
 (47 39 (:REWRITE STR::DEC-DIGIT-CHAR-LISTP-OF-CONS))
 (39 1 (:REWRITE NFIX-WHEN-NATP))
 (28 28 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (28 28 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (28 28 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (20 2 (:REWRITE VL2014::NATP-WHEN-POSP))
 (16 1 (:REWRITE POSP-REDEFINITION))
 (14 2 (:LINEAR LOWER-BOUND-OF-CAR-WHEN-NAT-LISTP))
 (12 12 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (12 12 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (12 12 (:REWRITE CONSP-BY-LEN))
 (12 6 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (10 1 (:REWRITE NFIX-WHEN-NOT-NATP))
 (8 8 (:TYPE-PRESCRIPTION NATP))
 (7 2 (:REWRITE NATP-WHEN-GTE-0))
 (6 6 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (6 6 (:REWRITE INTEGERP-WHEN-MEMBER-EQUAL-OF-INTEGER-LISTP))
 (6 6 (:REWRITE SET::IN-SET))
 (6 6 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (6 3 (:REWRITE VL2014::INTEGERP-WHEN-NATP))
 (6 2 (:REWRITE ZP-WHEN-INTEGERP))
 (6 2 (:REWRITE NATP-WHEN-INTEGERP))
 (6 2 (:REWRITE NATP-RW))
 (6 1 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (5 2 (:REWRITE ZP-WHEN-GT-0))
 (4 4 (:TYPE-PRESCRIPTION NAT-LISTP))
 (4 4 (:REWRITE NATP-WHEN-MEMBER-EQUAL-OF-NAT-LISTP))
 (4 4 (:REWRITE NAT-LISTP-WHEN-SUBSETP-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION POSP))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE NAT-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (2 2 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:META CANCEL_PLUS-LESSP-CORRECT))
 (2 1 (:REWRITE VL2014::NEGATIVE-WHEN-NATP))
 (2 1 (:REWRITE STR::DEC-DIGIT-CHAR-P-WHEN-NONZERO-DEC-DIGIT-CHAR-P))
 (1 1 (:TYPE-PRESCRIPTION ZP))
 (1 1 (:TYPE-PRESCRIPTION STR::NONZERO-DEC-DIGIT-CHAR-P$INLINE))
 (1 1 (:TYPE-PRESCRIPTION STR::DEC-DIGIT-CHAR-P$INLINE))
 (1 1 (:REWRITE MEMBER-SELF))
 )
(VL2014::VL-HTML-ENCODE-PUSH-OF-CHAR-FIX-CHAR1
 (96 96 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 )
(VL2014::VL-HTML-ENCODE-PUSH-CHAREQV-CONGRUENCE-ON-CHAR1)
(VL2014::VL-HTML-ENCODE-PUSH-OF-NFIX-COL
 (96 96 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 )
(VL2014::VL-HTML-ENCODE-PUSH-NAT-EQUIV-CONGRUENCE-ON-COL)
(VL2014::VL-HTML-ENCODE-PUSH-OF-POS-FIX-TABSIZE
 (224 224 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (52 18 (:REWRITE SET::DOUBLE-CONTAINMENT))
 (40 2 (:REWRITE NFIX-WHEN-NATP))
 (32 2 (:REWRITE POSP-REDEFINITION))
 (20 2 (:REWRITE VL2014::NATP-WHEN-POSP))
 (18 18 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (18 18 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (18 1 (:REWRITE POS-FIX-WHEN-POSP))
 (12 4 (:REWRITE ZP-WHEN-INTEGERP))
 (11 2 (:REWRITE NFIX-WHEN-NOT-NATP))
 (10 4 (:REWRITE ZP-WHEN-GT-0))
 (10 2 (:DEFINITION NOT))
 (9 9 (:TYPE-PRESCRIPTION NATP))
 (8 8 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (8 8 (:REWRITE INTEGERP-WHEN-MEMBER-EQUAL-OF-INTEGER-LISTP))
 (8 4 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (8 4 (:REWRITE VL2014::INTEGERP-WHEN-NATP))
 (7 2 (:REWRITE NATP-WHEN-GTE-0))
 (6 2 (:REWRITE NATP-WHEN-INTEGERP))
 (6 2 (:REWRITE NATP-RW))
 (4 4 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (4 4 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE NATP-WHEN-MEMBER-EQUAL-OF-NAT-LISTP))
 (4 4 (:REWRITE SET::IN-SET))
 (4 4 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (4 4 (:REWRITE CHARACTERP-WHEN-MEMBER-EQUAL-OF-CHARACTER-LISTP))
 (4 4 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (4 2 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (4 2 (:REWRITE CHAR-FIX-WHEN-CHARACTERP))
 (4 2 (:REWRITE CHAR-FIX-DEFAULT))
 (3 3 (:TYPE-PRESCRIPTION POSP))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (3 3 (:META CANCEL_PLUS-LESSP-CORRECT))
 (2 2 (:TYPE-PRESCRIPTION ZP))
 (2 2 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (2 2 (:REWRITE CONSP-BY-LEN))
 (2 1 (:REWRITE VL2014::NEGATIVE-WHEN-NATP))
 )
(VL2014::VL-HTML-ENCODE-PUSH-POS-EQUIV-CONGRUENCE-ON-TABSIZE)
(VL2014::VL-HTML-ENCODE-CHARS-AUX
 (38 10 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (19 2 (:REWRITE VL2014::NATP-WHEN-POSP))
 (16 8 (:REWRITE VL2014::MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-UNDER-IFF))
 (15 4 (:REWRITE VL2014::INTEGERP-WHEN-NATP))
 (12 2 (:REWRITE NATP-RW))
 (11 3 (:REWRITE ZP-WHEN-INTEGERP))
 (10 10 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (10 2 (:REWRITE STR::CHARACTER-LISTP-WHEN-DEC-DIGIT-CHAR-LISTP))
 (9 3 (:REWRITE ZP-WHEN-GT-0))
 (8 8 (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP))
 (8 8 (:REWRITE INTEGERP-WHEN-MEMBER-EQUAL-OF-INTEGER-LISTP))
 (8 1 (:REWRITE CHARACTER-LISTP-WHEN-NOT-CONSP))
 (7 2 (:REWRITE NATP-WHEN-GTE-0))
 (6 2 (:REWRITE NATP-WHEN-INTEGERP))
 (4 4 (:REWRITE SUBSETP-TRANS2))
 (4 4 (:REWRITE SUBSETP-TRANS))
 (4 4 (:REWRITE SUBSETP-MEMBER . 2))
 (4 4 (:REWRITE SUBSETP-MEMBER . 1))
 (4 4 (:REWRITE NATP-WHEN-MEMBER-EQUAL-OF-NAT-LISTP))
 (4 4 (:REWRITE MEMBER-SELF))
 (3 3 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE DEFAULT-CAR))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (3 3 (:META CANCEL_PLUS-LESSP-CORRECT))
 (2 2 (:REWRITE STR::DEC-DIGIT-CHAR-LISTP-WHEN-NOT-CONSP))
 (2 1 (:REWRITE VL2014::NEGATIVE-WHEN-NATP))
 (2 1 (:REWRITE STR::DEC-DIGIT-CHAR-LISTP-OF-CDR-WHEN-DEC-DIGIT-CHAR-LISTP))
 (1 1 (:TYPE-PRESCRIPTION ZP))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE CONSP-BY-LEN))
 )
(VL2014::NATP-OF-VL-HTML-ENCODE-CHARS-AUX.NEW-COL
 (54 4 (:REWRITE VL2014::NATP-WHEN-POSP))
 (48 2 (:REWRITE POSP-REDEFINITION))
 (39 1 (:REWRITE NFIX-WHEN-NATP))
 (24 7 (:REWRITE VL2014::INTEGERP-WHEN-NATP))
 (23 3 (:REWRITE ZP-OPEN))
 (14 14 (:REWRITE INTEGERP-WHEN-MEMBER-EQUAL-OF-INTEGER-LISTP))
 (14 4 (:REWRITE NATP-WHEN-GTE-0))
 (13 1 (:REWRITE CHAR-FIX-WHEN-CHARACTERP))
 (12 4 (:REWRITE NATP-WHEN-INTEGERP))
 (12 4 (:REWRITE NATP-RW))
 (11 3 (:REWRITE ZP-WHEN-INTEGERP))
 (11 2 (:REWRITE CHARACTERP-OF-CAR-WHEN-CHARACTER-LISTP))
 (10 1 (:REWRITE NFIX-WHEN-NOT-NATP))
 (9 3 (:REWRITE ZP-WHEN-GT-0))
 (8 8 (:REWRITE NATP-WHEN-MEMBER-EQUAL-OF-NAT-LISTP))
 (5 5 (:REWRITE DEFAULT-<-2))
 (5 5 (:REWRITE DEFAULT-<-1))
 (5 5 (:META CANCEL_PLUS-LESSP-CORRECT))
 (4 4 (:TYPE-PRESCRIPTION POSP))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (4 4 (:REWRITE CHARACTERP-WHEN-MEMBER-EQUAL-OF-CHARACTER-LISTP))
 (4 2 (:REWRITE VL2014::NEGATIVE-WHEN-NATP))
 (4 2 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (4 1 (:REWRITE STR::CHARACTER-LISTP-WHEN-DEC-DIGIT-CHAR-LISTP))
 (4 1 (:REWRITE CHAR-FIX-DEFAULT))
 (3 3 (:REWRITE DEFAULT-CAR))
 (3 3 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (2 2 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (2 2 (:TYPE-PRESCRIPTION STR::DEC-DIGIT-CHAR-LISTP))
 (2 2 (:TYPE-PRESCRIPTION CHARACTER-LISTP))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE CONSP-BY-LEN))
 (2 2 (:REWRITE CHARACTER-LISTP-WHEN-SUBSETP-EQUAL))
 (1 1 (:TYPE-PRESCRIPTION ZP))
 (1 1 (:REWRITE STR::DEC-DIGIT-CHAR-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE CHARACTER-LISTP-WHEN-NOT-CONSP))
 )
(VL2014::CHARACTER-LISTP-OF-VL-HTML-ENCODE-CHARS-AUX.NEW-ACC
 (77 1 (:REWRITE CHAR-FIX-WHEN-CHARACTERP))
 (66 24 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (56 4 (:REWRITE CHARACTERP-WHEN-MEMBER-EQUAL-OF-CHARACTER-LISTP))
 (48 7 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (39 1 (:REWRITE NFIX-WHEN-NATP))
 (38 2 (:REWRITE SUBSETP-CAR-MEMBER))
 (33 7 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (25 4 (:REWRITE CHARACTER-LISTP-WHEN-NOT-CONSP))
 (24 24 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (24 6 (:REWRITE STR::CHARACTER-LISTP-WHEN-DEC-DIGIT-CHAR-LISTP))
 (23 2 (:REWRITE CHARACTERP-OF-CAR-WHEN-CHARACTER-LISTP))
 (22 22 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (20 2 (:REWRITE VL2014::NATP-WHEN-POSP))
 (19 12 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (16 8 (:REWRITE VL2014::MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-UNDER-IFF))
 (16 1 (:REWRITE POSP-REDEFINITION))
 (12 12 (:TYPE-PRESCRIPTION STR::DEC-DIGIT-CHAR-LISTP))
 (10 1 (:REWRITE NFIX-WHEN-NOT-NATP))
 (9 9 (:REWRITE SUBSETP-TRANS2))
 (9 9 (:REWRITE SUBSETP-TRANS))
 (8 8 (:TYPE-PRESCRIPTION NATP))
 (8 8 (:REWRITE SUBSETP-MEMBER . 2))
 (8 8 (:REWRITE SUBSETP-MEMBER . 1))
 (8 8 (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP))
 (7 7 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (7 7 (:REWRITE CONSP-BY-LEN))
 (7 2 (:REWRITE NATP-WHEN-GTE-0))
 (6 6 (:REWRITE INTEGERP-WHEN-MEMBER-EQUAL-OF-INTEGER-LISTP))
 (6 6 (:REWRITE STR::DEC-DIGIT-CHAR-LISTP-WHEN-NOT-CONSP))
 (6 3 (:REWRITE VL2014::INTEGERP-WHEN-NATP))
 (6 2 (:REWRITE ZP-WHEN-INTEGERP))
 (6 2 (:REWRITE NATP-WHEN-INTEGERP))
 (6 2 (:REWRITE NATP-RW))
 (5 2 (:REWRITE ZP-WHEN-GT-0))
 (4 4 (:REWRITE NATP-WHEN-MEMBER-EQUAL-OF-NAT-LISTP))
 (4 4 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (4 1 (:REWRITE CHAR-FIX-DEFAULT))
 (2 2 (:TYPE-PRESCRIPTION POSP))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE MEMBER-SELF))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:META CANCEL_PLUS-LESSP-CORRECT))
 (2 1 (:REWRITE VL2014::NEGATIVE-WHEN-NATP))
 (1 1 (:TYPE-PRESCRIPTION ZP))
 )
(VL2014::VL-HTML-ENCODE-CHARS-AUX-OF-MAKE-CHARACTER-LIST-X
 (145 9 (:REWRITE STR::MAKE-CHARACTER-LIST-WHEN-CHARACTER-LISTP))
 (79 3 (:REWRITE NFIX-WHEN-NATP))
 (68 12 (:REWRITE STR::CHARACTER-LISTP-WHEN-DEC-DIGIT-CHAR-LISTP))
 (59 24 (:REWRITE DEFAULT-CDR))
 (57 6 (:REWRITE SET::DOUBLE-CONTAINMENT))
 (47 34 (:REWRITE DEFAULT-CAR))
 (40 4 (:REWRITE VL2014::NATP-WHEN-POSP))
 (35 11 (:REWRITE CHARACTER-LISTP-WHEN-NOT-CONSP))
 (34 34 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (32 2 (:REWRITE POSP-REDEFINITION))
 (30 3 (:REWRITE CHARACTER-LISTP-OF-CDR-WHEN-CHARACTER-LISTP))
 (26 26 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (26 26 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (22 22 (:REWRITE CHARACTER-LISTP-WHEN-SUBSETP-EQUAL))
 (21 3 (:REWRITE NFIX-WHEN-NOT-NATP))
 (16 16 (:TYPE-PRESCRIPTION NATP))
 (14 4 (:REWRITE NATP-WHEN-GTE-0))
 (12 12 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (12 12 (:REWRITE INTEGERP-WHEN-MEMBER-EQUAL-OF-INTEGER-LISTP))
 (12 6 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (12 6 (:REWRITE VL2014::INTEGERP-WHEN-NATP))
 (12 4 (:REWRITE ZP-WHEN-INTEGERP))
 (12 4 (:REWRITE NATP-WHEN-INTEGERP))
 (12 4 (:REWRITE NATP-RW))
 (11 11 (:REWRITE STR::DEC-DIGIT-CHAR-LISTP-WHEN-NOT-CONSP))
 (10 10 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (10 10 (:REWRITE CONSP-BY-LEN))
 (10 4 (:REWRITE ZP-WHEN-GT-0))
 (8 8 (:REWRITE NATP-WHEN-MEMBER-EQUAL-OF-NAT-LISTP))
 (6 6 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (6 6 (:REWRITE SET::IN-SET))
 (6 6 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (6 6 (:REWRITE CHARACTERP-WHEN-MEMBER-EQUAL-OF-CHARACTER-LISTP))
 (6 6 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (6 6 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (6 3 (:REWRITE STR::DEC-DIGIT-CHAR-LISTP-OF-CDR-WHEN-DEC-DIGIT-CHAR-LISTP))
 (6 1 (:REWRITE TRUE-LISTP-WHEN-SYMBOL-LISTP-REWRITE))
 (6 1 (:REWRITE TRUE-LISTP-WHEN-STRING-LISTP-REWRITE))
 (4 4 (:TYPE-PRESCRIPTION POSP))
 (4 4 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:META CANCEL_PLUS-LESSP-CORRECT))
 (4 2 (:REWRITE VL2014::NEGATIVE-WHEN-NATP))
 (4 1 (:REWRITE CHAR-FIX-DEFAULT))
 (2 2 (:TYPE-PRESCRIPTION ZP))
 (2 2 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL))
 (2 2 (:REWRITE STRING-LISTP-WHEN-SUBSETP-EQUAL))
 (2 1 (:REWRITE TRUE-LISTP-WHEN-CHARACTER-LISTP-REWRITE))
 (2 1 (:REWRITE TRUE-LISTP-WHEN-ATOM))
 (2 1 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (2 1 (:REWRITE STRING-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (1 1 (:REWRITE TRUE-LISTP-WHEN-SIGNED-BYTE-LISTP))
 )
(VL2014::VL-HTML-ENCODE-CHARS-AUX-CHARLISTEQV-CONGRUENCE-ON-X)
(VL2014::VL-HTML-ENCODE-CHARS-AUX-OF-NFIX-COL
 (40 4 (:REWRITE VL2014::NATP-WHEN-POSP))
 (32 2 (:REWRITE POSP-REDEFINITION))
 (25 5 (:REWRITE NFIX-WHEN-NOT-NATP))
 (16 16 (:TYPE-PRESCRIPTION NATP))
 (14 4 (:REWRITE NATP-WHEN-GTE-0))
 (14 2 (:REWRITE CHAR-FIX-WHEN-CHARACTERP))
 (12 12 (:REWRITE INTEGERP-WHEN-MEMBER-EQUAL-OF-INTEGER-LISTP))
 (12 6 (:REWRITE VL2014::INTEGERP-WHEN-NATP))
 (12 4 (:REWRITE ZP-WHEN-INTEGERP))
 (12 4 (:REWRITE NATP-WHEN-INTEGERP))
 (12 4 (:REWRITE NATP-RW))
 (11 2 (:REWRITE CHARACTERP-OF-CAR-WHEN-CHARACTER-LISTP))
 (10 4 (:REWRITE ZP-WHEN-GT-0))
 (8 8 (:REWRITE NATP-WHEN-MEMBER-EQUAL-OF-NAT-LISTP))
 (6 6 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (5 2 (:REWRITE CHAR-FIX-DEFAULT))
 (4 4 (:TYPE-PRESCRIPTION POSP))
 (4 4 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (4 4 (:REWRITE CHARACTERP-WHEN-MEMBER-EQUAL-OF-CHARACTER-LISTP))
 (4 4 (:META CANCEL_PLUS-LESSP-CORRECT))
 (4 2 (:REWRITE VL2014::NEGATIVE-WHEN-NATP))
 (4 2 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (4 1 (:REWRITE STR::CHARACTER-LISTP-WHEN-DEC-DIGIT-CHAR-LISTP))
 (2 2 (:TYPE-PRESCRIPTION ZP))
 (2 2 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (2 2 (:REWRITE CONSP-BY-LEN))
 (2 2 (:REWRITE CHARACTER-LISTP-WHEN-SUBSETP-EQUAL))
 (1 1 (:REWRITE STR::DEC-DIGIT-CHAR-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE CHARACTER-LISTP-WHEN-NOT-CONSP))
 )
(VL2014::VL-HTML-ENCODE-CHARS-AUX-NAT-EQUIV-CONGRUENCE-ON-COL)
(VL2014::VL-HTML-ENCODE-CHARS-AUX-OF-POS-FIX-TABSIZE
 (64 4 (:REWRITE POSP-REDEFINITION))
 (54 3 (:REWRITE POS-FIX-WHEN-POSP))
 (40 2 (:REWRITE NFIX-WHEN-NATP))
 (24 8 (:REWRITE ZP-WHEN-INTEGERP))
 (20 8 (:REWRITE ZP-WHEN-GT-0))
 (20 2 (:REWRITE VL2014::NATP-WHEN-POSP))
 (14 2 (:REWRITE CHAR-FIX-WHEN-CHARACTERP))
 (12 12 (:REWRITE INTEGERP-WHEN-MEMBER-EQUAL-OF-INTEGER-LISTP))
 (12 6 (:REWRITE VL2014::INTEGERP-WHEN-NATP))
 (11 11 (:TYPE-PRESCRIPTION NATP))
 (11 2 (:REWRITE NFIX-WHEN-NOT-NATP))
 (11 2 (:REWRITE CHARACTERP-OF-CAR-WHEN-CHARACTER-LISTP))
 (10 8 (:REWRITE DEFAULT-CAR))
 (9 1 (:REWRITE SET::DOUBLE-CONTAINMENT))
 (8 8 (:REWRITE ZP-OPEN))
 (8 8 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (8 6 (:REWRITE DEFAULT-CDR))
 (7 2 (:REWRITE NATP-WHEN-GTE-0))
 (6 2 (:REWRITE NATP-WHEN-INTEGERP))
 (6 2 (:REWRITE NATP-RW))
 (5 5 (:TYPE-PRESCRIPTION POSP))
 (5 5 (:REWRITE DEFAULT-<-2))
 (5 5 (:REWRITE DEFAULT-<-1))
 (5 5 (:META CANCEL_PLUS-LESSP-CORRECT))
 (5 2 (:REWRITE CHAR-FIX-DEFAULT))
 (4 4 (:TYPE-PRESCRIPTION ZP))
 (4 4 (:REWRITE NATP-WHEN-MEMBER-EQUAL-OF-NAT-LISTP))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (4 4 (:REWRITE CHARACTERP-WHEN-MEMBER-EQUAL-OF-CHARACTER-LISTP))
 (4 2 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (4 1 (:REWRITE STR::CHARACTER-LISTP-WHEN-DEC-DIGIT-CHAR-LISTP))
 (2 2 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (2 2 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (2 2 (:REWRITE CONSP-BY-LEN))
 (2 2 (:REWRITE CHARACTER-LISTP-WHEN-SUBSETP-EQUAL))
 (2 1 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (2 1 (:REWRITE VL2014::NEGATIVE-WHEN-NATP))
 (1 1 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (1 1 (:REWRITE SET::IN-SET))
 (1 1 (:REWRITE STR::DEC-DIGIT-CHAR-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE CHARACTER-LISTP-WHEN-NOT-CONSP))
 (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(VL2014::VL-HTML-ENCODE-CHARS-AUX-POS-EQUIV-CONGRUENCE-ON-TABSIZE)
(VL2014::VL-HTML-ENCODE-STRING-AUX
 (9 3 (:TYPE-PRESCRIPTION CONSP-NTHCDR))
 (3 3 (:TYPE-PRESCRIPTION NFIX))
 (3 3 (:TYPE-PRESCRIPTION LEN))
 )
(VL2014::VL-HTML-ENCODE-STRING-AUX
 (1614 8 (:DEFINITION NTH))
 (546 16 (:REWRITE VL2014::NTH-WHEN-TOO-BIG))
 (521 115 (:REWRITE LEN-WHEN-ATOM))
 (422 16 (:REWRITE NTH-WITH-LARGE-INDEX))
 (366 16 (:REWRITE NTH-WHEN-TOO-LARGE-CHEAP))
 (316 40 (:REWRITE STR::EXPLODE-UNDER-IFF))
 (298 64 (:REWRITE ZP-WHEN-GT-0))
 (263 3 (:REWRITE CHARACTERP-OF-CAR-WHEN-CHARACTER-LISTP))
 (262 24 (:LINEAR VL2014::LEN-OF-CDR-STRONG))
 (248 16 (:REWRITE VL2014::NTH-WHEN-ZP))
 (224 181 (:REWRITE DEFAULT-<-2))
 (222 3 (:REWRITE CHARACTER-LISTP-OF-CDR-WHEN-CHARACTER-LISTP))
 (206 181 (:REWRITE DEFAULT-<-1))
 (198 198 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (196 196 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (192 192 (:META CANCEL_PLUS-LESSP-CORRECT))
 (188 16 (:REWRITE NTH-WHEN-ZP))
 (177 82 (:REWRITE DEFAULT-CDR))
 (174 16 (:REWRITE NTH-WHEN-ATOM))
 (174 16 (:REWRITE VL2014::NTH-OF-ATOM))
 (138 3 (:REWRITE VL2014::STRINGP-WHEN-TRUE-LISTP))
 (128 9 (:REWRITE NTHCDR-WHEN-ATOM))
 (122 9 (:REWRITE NTHCDR-WHEN-ZP))
 (118 82 (:REWRITE NFIX-WHEN-NOT-NATP))
 (112 112 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (112 112 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (112 112 (:LINEAR LEN-WHEN-PREFIXP))
 (108 36 (:REWRITE VL2014::|(< c2 (+ c1 a))|))
 (95 10 (:REWRITE VL2014::NATP-WHEN-POSP))
 (93 3 (:REWRITE CHARACTER-LISTP-OF-NTHCDR))
 (89 81 (:REWRITE SET::DOUBLE-CONTAINMENT))
 (89 43 (:TYPE-PRESCRIPTION CONSP-NTHCDR))
 (81 81 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (81 81 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (71 18 (:REWRITE VL2014::INTEGERP-WHEN-NATP))
 (60 10 (:REWRITE NATP-RW))
 (60 9 (:REWRITE CHARACTER-LISTP-WHEN-NOT-CONSP))
 (57 12 (:REWRITE STR::CHARACTER-LISTP-WHEN-DEC-DIGIT-CHAR-LISTP))
 (56 56 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (56 56 (:LINEAR INDEX-OF-<-LEN))
 (36 36 (:REWRITE INTEGERP-WHEN-MEMBER-EQUAL-OF-INTEGER-LISTP))
 (35 27 (:REWRITE DEFAULT-+-2))
 (35 27 (:REWRITE DEFAULT-+-1))
 (35 10 (:REWRITE NATP-WHEN-GTE-0))
 (34 34 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 (33 3 (:REWRITE TRUE-LISTP-WHEN-SYMBOL-LISTP-REWRITE))
 (30 10 (:REWRITE NATP-WHEN-INTEGERP))
 (24 3 (:REWRITE TRUE-LISTP-WHEN-STRING-LISTP-REWRITE))
 (24 3 (:REWRITE TRUE-LISTP-WHEN-CHARACTER-LISTP-REWRITE))
 (24 3 (:REWRITE TRUE-LISTP-WHEN-ATOM))
 (23 2 (:REWRITE |(< 0 (len x))|))
 (21 1 (:REWRITE CHAR-FIX-DEFAULT))
 (20 20 (:REWRITE NATP-WHEN-MEMBER-EQUAL-OF-NAT-LISTP))
 (18 18 (:REWRITE CHARACTER-LISTP-WHEN-SUBSETP-EQUAL))
 (18 13 (:REWRITE DEFAULT-CAR))
 (18 3 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (18 1 (:REWRITE LIST-EQUIV-WHEN-ATOM-RIGHT))
 (18 1 (:REWRITE LIST-EQUIV-WHEN-ATOM-LEFT))
 (13 13 (:REWRITE ZP-OPEN))
 (13 13 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (12 9 (:REWRITE STR::DEC-DIGIT-CHAR-LISTP-WHEN-NOT-CONSP))
 (9 9 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (9 9 (:REWRITE OPEN-SMALL-NTHCDR))
 (8 8 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (8 8 (:REWRITE NTH-WHEN-PREFIXP))
 (8 8 (:REWRITE VL2014::NTH-OF-EXPLODE-WHEN-CHAR-FIX-KNOWN))
 (8 8 (:REWRITE DEFAULT-UNARY-MINUS))
 (8 4 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (6 6 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL))
 (6 6 (:REWRITE STRINGP-WHEN-MEMBER-EQUAL-OF-STRING-LISTP))
 (6 6 (:REWRITE STRING-LISTP-WHEN-SUBSETP-EQUAL))
 (6 6 (:REWRITE CHARACTERP-WHEN-MEMBER-EQUAL-OF-CHARACTER-LISTP))
 (6 3 (:REWRITE SYMBOL-LISTP-WHEN-BOOLEAN-LISTP))
 (6 3 (:REWRITE STR::DEC-DIGIT-CHAR-LISTP-OF-NTHCDR))
 (6 3 (:REWRITE STR::DEC-DIGIT-CHAR-LISTP-OF-CDR-WHEN-DEC-DIGIT-CHAR-LISTP))
 (4 4 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (4 4 (:REWRITE SET::IN-SET))
 (3 3 (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (3 3 (:REWRITE TRUE-LISTP-WHEN-SIGNED-BYTE-LISTP))
 (3 3 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 2))
 (3 3 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 1))
 (3 3 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (3 3 (:REWRITE VL2014::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 2))
 (3 3 (:REWRITE VL2014::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 1))
 (3 3 (:REWRITE STRING-LISTP-WHEN-NOT-CONSP))
 (3 3 (:REWRITE FN-CHECK-DEF-FORMALS))
 (3 3 (:REWRITE CONSP-BY-LEN))
 (3 3 (:REWRITE CHARACTER-LISTP-OF-EXPLODE))
 (2 1 (:REWRITE PREFIXP-WHEN-PREFIXP))
 (1 1 (:REWRITE VL2014::VL-HTML-ENCODE-PUSH-OF-CHAR-FIX-CHAR1))
 (1 1 (:REWRITE VL2014::VL-HTML-ENCODE-NEXT-COL$INLINE-OF-CHAR-FIX-CHAR1))
 (1 1 (:REWRITE SUBLISTP-COMPLETE))
 (1 1 (:REWRITE PREFIXP-TRANSITIVE . 2))
 (1 1 (:REWRITE PREFIXP-TRANSITIVE . 1))
 (1 1 (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
 (1 1 (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
 )
(VL2014::VL-HTML-ENCODE-STRING)
(VL2014::STRINGP-OF-VL-HTML-ENCODE-STRING)
(VL2014::VL-HTML-ENCODE-STRING-OF-STR-FIX-X
 (12 12 (:TYPE-PRESCRIPTION CONSP-REVERSE))
 )
(VL2014::VL-HTML-ENCODE-STRING-STREQV-CONGRUENCE-ON-X)
(VL2014::VL-HTML-ENCODE-STRING-OF-POS-FIX-TABSIZE)
(VL2014::VL-HTML-ENCODE-STRING-POS-EQUIV-CONGRUENCE-ON-TABSIZE)
