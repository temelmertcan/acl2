(FM9001::UNBOUND-IN-BODY)
(FM9001::UNBOUND-IN-BODY-ATOM)
(FM9001::UNBOUND-IN-BODY-LISTP
 (15 5 (:DEFINITION MEMBER-EQUAL))
 (8 8 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE FM9001::UNBOUND-IN-BODY-ATOM))
 )
(FM9001::ALL-UNBOUND-IN-BODY)
(FM9001::ALL-UNBOUND-IN-BODY-ATOM)
(FM9001::ALL-UNBOUND-IN-BODY-LISTP
 (20 5 (:REWRITE FM9001::DISJOINT-ATOM))
 (10 10 (:DEFINITION ATOM))
 (6 6 (:REWRITE FM9001::ALL-UNBOUND-IN-BODY-ATOM))
 (5 5 (:TYPE-PRESCRIPTION ATOM))
 (3 3 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-CAR))
 )
(FM9001::ALL-UNBOUND-IN-BODY-APPEND
 (143 38 (:REWRITE FM9001::DISJOINT-ATOM))
 (40 10 (:DEFINITION BINARY-APPEND))
 (36 36 (:REWRITE DEFAULT-CAR))
 (35 35 (:TYPE-PRESCRIPTION ATOM))
 (25 25 (:REWRITE DEFAULT-CDR))
 (20 20 (:REWRITE APPEND-WHEN-NOT-CONSP))
 )
(FM9001::ALL-UNBOUND-IN-BODY-CONS
 (180 45 (:REWRITE FM9001::DISJOINT-ATOM))
 (81 81 (:REWRITE DEFAULT-CDR))
 (76 76 (:REWRITE DEFAULT-CAR))
 (75 25 (:DEFINITION MEMBER-EQUAL))
 (45 45 (:TYPE-PRESCRIPTION ATOM))
 )
(FM9001::ALL-UNBOUND-IN-BODY-ATOM-NAMES
 (5 5 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE DEFAULT-CDR))
 )
(FM9001::UNBOUND-IN-BODY-SE-OCC
 (381 24 (:REWRITE FM9001::SINGLETON-ASSOC-EQ-VALUES))
 (275 25 (:DEFINITION PAIRLIS$))
 (264 8 (:REWRITE FM9001::ASSOC-EQ-VALUES-APPEND-WHEN-DISJOINT-2))
 (261 186 (:REWRITE DEFAULT-CAR))
 (231 156 (:REWRITE DEFAULT-CDR))
 (216 32 (:REWRITE FM9001::DISJOINT-ATOM))
 (152 8 (:REWRITE FM9001::ASSOC-EQ-VALUES-APPEND-WHEN-DISJOINT-1))
 (152 8 (:REWRITE FM9001::ASSOC-EQ-VALUES-APPEND-PAIRLIS$-WHEN-SUBSET))
 (150 150 (:TYPE-PRESCRIPTION FM9001::SE))
 (147 147 (:TYPE-PRESCRIPTION LEN))
 (129 129 (:TYPE-PRESCRIPTION PAIRLIS$))
 (120 20 (:DEFINITION BINARY-APPEND))
 (120 16 (:REWRITE FM9001::STRIP-CARS-PAIRLIS$))
 (120 8 (:DEFINITION SUBSETP-EQUAL))
 (105 21 (:DEFINITION LEN))
 (97 40 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (96 16 (:DEFINITION STRIP-CARS))
 (88 88 (:TYPE-PRESCRIPTION STRIP-CARS))
 (84 84 (:LINEAR LEN-WHEN-PREFIXP))
 (64 64 (:TYPE-PRESCRIPTION FM9001::DISJOINT))
 (64 8 (:DEFINITION TRUE-LISTP))
 (57 11 (:DEFINITION MEMBER-EQUAL))
 (56 8 (:REWRITE FM9001::ASSOC-EQ-VALUES-APPEND-PAIRLIS$-WHEN-DISJOINT-2))
 (56 8 (:REWRITE FM9001::ASSOC-EQ-VALUES-APPEND-PAIRLIS$-WHEN-DISJOINT-1))
 (48 16 (:REWRITE FM9001::BVP-IS-TRUE-LISTP))
 (42 42 (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 (42 21 (:REWRITE DEFAULT-+-2))
 (40 40 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (40 40 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (32 32 (:TYPE-PRESCRIPTION FM9001::BVP))
 (32 32 (:TYPE-PRESCRIPTION ATOM))
 (24 24 (:REWRITE FM9001::ASSOC-EQ-VALUES-ATOM))
 (21 21 (:REWRITE DEFAULT-+-1))
 (16 16 (:REWRITE FM9001::SUBSETP-TRANSITIVITY))
 (5 5 (:REWRITE FM9001::ASSOC-EQ-VALUE-PAIRLIS$-NOT-MEMBER))
 (3 3 (:TYPE-PRESCRIPTION FM9001::SE-OCC-INDUCT))
 )
(FM9001::ALL-UNBOUND-IN-BODY-SE-OCC
 (612 51 (:REWRITE FM9001::SINGLETON-ASSOC-EQ-VALUES))
 (429 13 (:REWRITE FM9001::ASSOC-EQ-VALUES-APPEND-WHEN-DISJOINT-2))
 (363 55 (:REWRITE FM9001::DISJOINT-ATOM))
 (286 211 (:REWRITE DEFAULT-CAR))
 (275 25 (:DEFINITION PAIRLIS$))
 (268 193 (:REWRITE DEFAULT-CDR))
 (247 13 (:REWRITE FM9001::ASSOC-EQ-VALUES-APPEND-WHEN-DISJOINT-1))
 (247 13 (:REWRITE FM9001::ASSOC-EQ-VALUES-APPEND-PAIRLIS$-WHEN-SUBSET))
 (231 231 (:TYPE-PRESCRIPTION LEN))
 (195 26 (:REWRITE FM9001::STRIP-CARS-PAIRLIS$))
 (195 13 (:DEFINITION SUBSETP-EQUAL))
 (165 165 (:TYPE-PRESCRIPTION PAIRLIS$))
 (165 33 (:DEFINITION LEN))
 (156 26 (:DEFINITION STRIP-CARS))
 (150 150 (:TYPE-PRESCRIPTION FM9001::SE))
 (150 25 (:DEFINITION BINARY-APPEND))
 (143 143 (:TYPE-PRESCRIPTION STRIP-CARS))
 (132 132 (:LINEAR LEN-WHEN-PREFIXP))
 (113 50 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (105 15 (:REWRITE FM9001::ASSOC-EQ-VALUES-APPEND-PAIRLIS$-WHEN-DISJOINT-2))
 (104 13 (:DEFINITION TRUE-LISTP))
 (78 26 (:REWRITE FM9001::BVP-IS-TRUE-LISTP))
 (78 13 (:DEFINITION MEMBER-EQUAL))
 (66 66 (:LINEAR FM9001::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 (66 33 (:REWRITE DEFAULT-+-2))
 (65 65 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (65 65 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (65 65 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (55 55 (:TYPE-PRESCRIPTION ATOM))
 (52 52 (:TYPE-PRESCRIPTION FM9001::BVP))
 (49 49 (:REWRITE FM9001::ASSOC-EQ-VALUES-ATOM))
 (33 33 (:REWRITE DEFAULT-+-1))
 (26 26 (:REWRITE FM9001::SUBSETP-TRANSITIVITY))
 (11 11 (:REWRITE FM9001::ALL-UNBOUND-IN-BODY-ATOM-NAMES))
 (3 3 (:TYPE-PRESCRIPTION FM9001::SE-OCC-INDUCT))
 )
