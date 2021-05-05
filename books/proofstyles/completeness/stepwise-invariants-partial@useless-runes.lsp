(EXISTS-SOME-EXITPOINT)
(EXISTS-SOME-EXITPOINT-SUFF)
(INV)
(INV-SUFF
 (6 6 (:DEFINITION MV-NTH))
 )
(CUTPOINT-INDUCTION
 (3 3 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(CLOCK-FN-TAIL-INV
 (115 115 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (82 34 (:REWRITE FOLD-CONSTS-IN-+))
 (76 13 (:REWRITE ZP-OPEN))
 (72 70 (:REWRITE DEFAULT-+-2))
 (71 70 (:REWRITE DEFAULT-+-1))
 (63 3 (:REWRITE NATP-POSP))
 (48 12 (:REWRITE <-0-+-NEGATIVE-1))
 (31 31 (:REWRITE DEFAULT-<-2))
 (31 31 (:REWRITE DEFAULT-<-1))
 (29 5 (:REWRITE NATP-RW))
 (27 3 (:REWRITE POSP-RW))
 (24 6 (:REWRITE <-+-NEGATIVE-0-1))
 (12 12 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(CLOCK-FN-IS-NATP
 (6 6 (:TYPE-PRESCRIPTION |clock fn is natp|))
 (3 3 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 )
(CLOCK-FN-PROVIDE-EXITPOINT
 (24 4 (:DEFINITION RUN-FN))
 (12 4 (:REWRITE ZP-OPEN))
 (7 6 (:REWRITE DEFAULT-+-2))
 (7 6 (:REWRITE DEFAULT-+-1))
 (6 6 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 3 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:META CANCEL_PLUS-LESSP-CORRECT))
 (2 2 (:REWRITE NATP-RW))
 (2 2 (:DEFINITION CLOCK-FN-TAIL-DEF))
 (1 1 (:LINEAR |clock fn is minimal|))
 )
(CLOCK-FN-IS-MINIMAL
 (6 6 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (4 1 (:DEFINITION RUN-FN))
 (3 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-+-1))
 (2 2 (:TYPE-PRESCRIPTION |clock fn is natp|))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE NATP-RW))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:META CANCEL_PLUS-LESSP-CORRECT))
 (1 1 (:LINEAR |clock fn is minimal|))
 (1 1 (:DEFINITION CLOCK-FN-TAIL-DEF))
 )
(|pre implies inv|
 (20 20 (:TYPE-PRESCRIPTION |clock fn is natp|))
 (15 2 (:REWRITE DEFAULT-<-1))
 (7 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (5 1 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:META CANCEL_PLUS-LESSP-CORRECT))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(INDUCTION-HINT
 (3 3 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(STEP-FN-RUN-FN-IS-RUN-FN-STEP-FN
 (34 6 (:REWRITE ZP-OPEN))
 (16 4 (:REWRITE <-0-+-NEGATIVE-1))
 (12 4 (:REWRITE FOLD-CONSTS-IN-+))
 (10 10 (:REWRITE DEFAULT-+-2))
 (10 10 (:REWRITE DEFAULT-+-1))
 (8 8 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (8 8 (:META CANCEL_PLUS-LESSP-CORRECT))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(|inv implies step-fn inv|
 (44 22 (:REWRITE DEFAULT-<-1))
 (26 2 (:LINEAR |clock fn is minimal|))
 (24 20 (:REWRITE DEFAULT-+-2))
 (22 22 (:REWRITE DEFAULT-<-2))
 (22 22 (:META CANCEL_PLUS-LESSP-CORRECT))
 (20 20 (:REWRITE DEFAULT-+-1))
 (19 19 (:REWRITE |pre implies inv|))
 (19 10 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (14 14 (:REWRITE DEFAULT-CDR))
 (8 8 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (8 8 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (8 2 (:LINEAR CLOCK-FN-IS-MINIMAL))
 (6 6 (:REWRITE NATP-RW))
 )
(|inv and exitpoint implies post|
 (424 424 (:TYPE-PRESCRIPTION |clock fn is natp|))
 (424 424 (:TYPE-PRESCRIPTION CLOCK-FN-IS-NATP))
 (83 18 (:REWRITE DEFAULT-<-1))
 (41 7 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (28 28 (:REWRITE DEFAULT-CAR))
 (18 18 (:REWRITE DEFAULT-<-2))
 (18 18 (:META CANCEL_PLUS-LESSP-CORRECT))
 (13 13 (:REWRITE DEFAULT-CDR))
 (12 12 (:REWRITE DEFAULT-+-2))
 (12 12 (:REWRITE DEFAULT-+-1))
 (9 9 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (9 9 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (9 1 (:REWRITE |partial correctness|))
 (8 8 (:REWRITE |pre implies inv|))
 (8 8 (:LINEAR CLOCK-FN-IS-MINIMAL))
 (7 5 (:REWRITE NATP-RW))
 (1 1 (:REWRITE CLOCK-FN-IS-NATP))
 )
