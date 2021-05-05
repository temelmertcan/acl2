(LRAT::FORMULA-P-REVAPPEND
 (51 42 (:REWRITE DEFAULT-CAR))
 (42 33 (:REWRITE DEFAULT-CDR))
 (17 17 (:REWRITE DEFAULT-<-2))
 (17 17 (:REWRITE DEFAULT-<-1))
 )
(LRAT::NEGATE-CUBE-NEGATE-CUBE
 (34 34 (:REWRITE DEFAULT-CDR))
 (34 34 (:REWRITE DEFAULT-CAR))
 (30 19 (:REWRITE DEFAULT-UNARY-MINUS))
 (11 11 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(LRAT::LEMMA-1)
(LRAT::LEMMA-2)
(LRAT::FORMULA-EQUIV)
(LRAT::FORMULA-EQUIV-NECC)
(LRAT::FORMULA-EQUIV-PRESERVES-SATISFIABLE-1
 (32 4 (:DEFINITION HONS-ASSOC-EQUAL))
 (22 16 (:REWRITE DEFAULT-CDR))
 (16 16 (:REWRITE DEFAULT-CAR))
 (4 4 (:DEFINITION HONS-EQUAL))
 (3 3 (:REWRITE LRAT::TRUTH-MONOTONE-ALT))
 (3 3 (:REWRITE LRAT::TRUTH-MONOTONE))
 )
(LRAT::FORMULA-EQUIV-PRESERVES-SATISFIABLE
 (4 4 (:REWRITE LRAT::SOUNDNESS-MAIN))
 (4 4 (:REWRITE LRAT::SOUNDNESS-HELPER-2))
 (4 4 (:REWRITE LRAT::SOUNDNESS-HELPER-1))
 (3 3 (:REWRITE LRAT::TRUTH-MONOTONE-ALT))
 (3 3 (:REWRITE LRAT::TRUTH-MONOTONE))
 )
(LRAT::NO-DUPLICATESP-EQUAL-STRIP-CARS-REVAPPEND
 (326 231 (:REWRITE DEFAULT-CAR))
 (217 179 (:REWRITE DEFAULT-CDR))
 (90 45 (:TYPE-PRESCRIPTION TRUE-LISTP-REVAPPEND-TYPE-PRESCRIPTION))
 (82 82 (:REWRITE LRAT::MEMBER-NEGATE-IMPLIES-MEMBER-ASSIGNMENT))
 (45 45 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (45 45 (:TYPE-PRESCRIPTION REVAPPEND))
 )
(LRAT::ORDERED-FORMULA-P1-IMPLIES-NOT-MEMBER-EQUAL
 (36 35 (:REWRITE DEFAULT-CAR))
 (31 20 (:REWRITE DEFAULT-<-2))
 (26 20 (:REWRITE DEFAULT-<-1))
 (17 17 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (16 15 (:REWRITE DEFAULT-CDR))
 (9 9 (:REWRITE LRAT::MEMBER-NEGATE-IMPLIES-MEMBER-ASSIGNMENT))
 )
(LRAT::ORDERED-FORMULA-P1-IMPLIES-NO-DUPLICATESP-EQUAL
 (31 30 (:REWRITE DEFAULT-CAR))
 (22 20 (:REWRITE DEFAULT-CDR))
 (15 10 (:REWRITE DEFAULT-<-2))
 (12 3 (:DEFINITION MEMBER-EQUAL))
 (10 10 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE LRAT::MEMBER-NEGATE-IMPLIES-MEMBER-ASSIGNMENT))
 (5 5 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 3 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 )
(LRAT::ORDERED-FORMULA-P-IMPLIES-NO-DUPLICATESP-EQUAL-STRIP-CARS
 (23 22 (:REWRITE DEFAULT-CAR))
 (15 13 (:REWRITE DEFAULT-CDR))
 (4 1 (:DEFINITION MEMBER-EQUAL))
 (2 2 (:REWRITE LRAT::MEMBER-NEGATE-IMPLIES-MEMBER-ASSIGNMENT))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (1 1 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 )
(LRAT::SOUNDNESS-MAIN-ALT)
(LRAT::VERIFY-FOR-CUBE-SOUNDNESS-MAIN
 (1284 828 (:REWRITE DEFAULT-CDR))
 (463 431 (:REWRITE DEFAULT-CAR))
 (135 127 (:REWRITE DEFAULT-<-1))
 (127 127 (:REWRITE DEFAULT-<-2))
 (78 11 (:REWRITE LRAT::FORMULA-EQUIV-PRESERVES-SATISFIABLE))
 (8 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
