(FLAT::COMMUTATIVITY-2-OF-+)
(FLAT::ASSOCIATE-CONSTANTS-LEFT-+)
(FLAT::MINUS-INVERSE-+-A)
(FLAT::MINUS-INVERSE-+-B)
(FLAT::TEST)
(FLAT::BASE)
(FLAT::ST)
(FLAT::H)
(FLAT::H-IS-MONOTONIC-2)
(FLAT::H-IS-MONOTONIC-2-A)
(FLAT::F-CHAIN)
(FLAT::BASE-OF-F-CHAIN=$BOTTOM$
 (1 1 (:REWRITE ZP-OPEN))
 )
(FLAT::F-CHAIN-IS-$<=$-CHAIN
 (29 29 (:REWRITE DEFAULT-<-2))
 (29 29 (:REWRITE DEFAULT-<-1))
 (21 21 (:REWRITE FLAT::$BOTTOM$-BASED-CHAIN-I>0))
 (13 13 (:REWRITE DEFAULT-+-2))
 (13 13 (:REWRITE DEFAULT-+-1))
 )
(FLAT::LUB-F-CHAIN-I-REWRITE
 (34 4 (:REWRITE FLAT::BASE-OF-F-CHAIN=$BOTTOM$))
 (7 7 (:REWRITE DEFAULT-<-2))
 (7 7 (:REWRITE DEFAULT-<-1))
 (7 7 (:REWRITE FLAT::$BOTTOM$-BASED-CHAIN-I>0))
 (5 5 (:TYPE-PRESCRIPTION ZP))
 (4 4 (:REWRITE FLAT::H-IS-MONOTONIC-2-A))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(FLAT::LUB-F-CHAIN-NAT-I)
(FLAT::LUB-F-CHAIN)
(FLAT::LUB-F-CHAIN-IS-UPPER-BOUND
 (421 71 (:REWRITE ZP-OPEN))
 (103 103 (:REWRITE DEFAULT-<-2))
 (103 103 (:REWRITE DEFAULT-<-1))
 (98 98 (:REWRITE FLAT::$BOTTOM$-BASED-CHAIN-I>0))
 (42 42 (:REWRITE FLAT::H-IS-MONOTONIC-2-A))
 (21 21 (:REWRITE DEFAULT-+-2))
 (21 21 (:REWRITE DEFAULT-+-1))
 )
(FLAT::F)
(FLAT::G-CHAIN)
(FLAT::UB-G-CHAIN)
(FLAT::G-CHAIN-$<=$-UB-G-CHAIN
 (118 117 (:REWRITE DEFAULT-<-1))
 (117 117 (:REWRITE DEFAULT-<-2))
 (107 107 (:REWRITE FLAT::$BOTTOM$-BASED-CHAIN-I>0))
 (64 64 (:TYPE-PRESCRIPTION ZP))
 (24 24 (:REWRITE DEFAULT-+-2))
 (24 24 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(FLAT::SKOLEM-F)
(FLAT::UB-G-CHAIN-=-G-CHAIN-SKOLEM-F
 (141 15 (:REWRITE FLAT::BASE-OF-F-CHAIN=$BOTTOM$))
 (137 19 (:REWRITE ZP-OPEN))
 (135 15 (:REWRITE FLAT::LUB-F-CHAIN-I-REWRITE))
 (61 19 (:DEFINITION NOT))
 (36 36 (:REWRITE DEFAULT-<-2))
 (36 36 (:REWRITE DEFAULT-<-1))
 (33 33 (:REWRITE FLAT::$BOTTOM$-BASED-CHAIN-I>0))
 (16 16 (:REWRITE FLAT::H-IS-MONOTONIC-2-A))
 (14 14 (:TYPE-PRESCRIPTION ZP))
 (6 6 (:REWRITE DEFAULT-+-2))
 (6 6 (:REWRITE DEFAULT-+-1))
 )
(FLAT::LUB-F-CHAIN=UB-G-CHAIN
 (1067 170 (:REWRITE ZP-OPEN))
 (271 271 (:REWRITE DEFAULT-<-2))
 (271 271 (:REWRITE DEFAULT-<-1))
 (251 251 (:REWRITE FLAT::$BOTTOM$-BASED-CHAIN-I>0))
 (129 129 (:REWRITE FLAT::H-IS-MONOTONIC-2-A))
 (60 60 (:REWRITE DEFAULT-+-2))
 (60 60 (:REWRITE DEFAULT-+-1))
 (3 1 (:REWRITE FLAT::H-IS-MONOTONIC-2))
 )
(FLAT::GENERIC-PRIMITIVE-RECURSIVE-F
 (142 135 (:REWRITE DEFAULT-<-1))
 (135 135 (:REWRITE DEFAULT-<-2))
 (109 109 (:REWRITE FLAT::$BOTTOM$-BASED-CHAIN-I>0))
 (66 66 (:REWRITE FLAT::H-IS-MONOTONIC-2-A))
 (43 43 (:TYPE-PRESCRIPTION ZP))
 (22 22 (:REWRITE DEFAULT-+-2))
 (22 22 (:REWRITE DEFAULT-+-1))
 (7 7 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
