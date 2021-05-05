(SUBSETP-EQUAL-CONS
 (43 43 (:REWRITE DEFAULT-CAR))
 (22 22 (:REWRITE DEFAULT-CDR))
 )
(SUBSETP-EQUAL-REFLEXIVE
 (22 22 (:REWRITE DEFAULT-CAR))
 (19 19 (:REWRITE DEFAULT-CDR))
 )
(SUBSETP-EQUAL-TRANSITIVE
 (116 116 (:REWRITE DEFAULT-CAR))
 (89 89 (:REWRITE DEFAULT-CDR))
 )
(SUBSETP-EQUAL-APPEND-CROCK
 (85 55 (:REWRITE DEFAULT-CAR))
 (59 41 (:REWRITE DEFAULT-CDR))
 )
(SUBSETP-EQUAL-APPEND2
 (107 98 (:REWRITE DEFAULT-CAR))
 (94 47 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (80 74 (:REWRITE DEFAULT-CDR))
 (47 47 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (47 47 (:TYPE-PRESCRIPTION BINARY-APPEND))
 )
(SUBSETP-EQUAL-ADJOIN-EQUAL1
 (55 55 (:REWRITE DEFAULT-CAR))
 (42 42 (:REWRITE DEFAULT-CDR))
 )
(SUBSETP-EQUAL-ADJOIN-EQUAL2
 (23 3 (:DEFINITION SUBSETP-EQUAL))
 (17 5 (:DEFINITION MEMBER-EQUAL))
 (8 8 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE DEFAULT-CAR))
 )
(SUBSETP-EQUAL-INTERSECTION-EQUAL
 (211 209 (:REWRITE DEFAULT-CAR))
 (168 167 (:REWRITE DEFAULT-CDR))
 )
(SUBSETP-EQUAL-SET-DIFFERENCE-EQUAL
 (229 227 (:REWRITE DEFAULT-CAR))
 (180 179 (:REWRITE DEFAULT-CDR))
 )
(SUBSETP-EQUAL-UNION-EQUAL
 (313 309 (:REWRITE DEFAULT-CAR))
 (252 249 (:REWRITE DEFAULT-CDR))
 (106 106 (:TYPE-PRESCRIPTION UNION-EQUAL))
 )
(SET-EQUAL-REFLEXIVE)
(SET-EQUAL-SYMMETRIC
 (12 4 (:DEFINITION MEMBER-EQUAL))
 (8 8 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE DEFAULT-CAR))
 )
(SET-EQUAL-TRANSITIVE
 (36 12 (:DEFINITION MEMBER-EQUAL))
 (24 24 (:REWRITE DEFAULT-CDR))
 (24 24 (:REWRITE DEFAULT-CAR))
 )
(MEMBERP-EQUAL-SUBSETP-EQUAL
 (28 28 (:REWRITE DEFAULT-CAR))
 (16 16 (:REWRITE DEFAULT-CDR))
 )
(MEMBERP-EQUAL-SET-EQUAL)
(MEMBERP-EQUAL-ADJOIN-EQUAL
 (11 11 (:REWRITE DEFAULT-CAR))
 (10 10 (:REWRITE DEFAULT-CDR))
 )
(MEMBERP-EQUAL-INTERSECTION-EQUAL
 (97 94 (:REWRITE DEFAULT-CAR))
 (88 85 (:REWRITE DEFAULT-CDR))
 )
(MEMBERP-EQUAL-SET-DIFFERENCE-EQUAL
 (97 94 (:REWRITE DEFAULT-CAR))
 (88 85 (:REWRITE DEFAULT-CDR))
 )
(MEMBERP-EQUAL-UNION-EQUAL
 (97 94 (:REWRITE DEFAULT-CAR))
 (86 83 (:REWRITE DEFAULT-CDR))
 (38 38 (:TYPE-PRESCRIPTION UNION-EQUAL))
 )
(SETP-EQUAL-CONS
 (15 5 (:DEFINITION MEMBER-EQUAL))
 (14 14 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE DEFAULT-CAR))
 )
(SETP-EQUAL-ADJOIN-EQUAL
 (16 16 (:REWRITE DEFAULT-CDR))
 (10 10 (:REWRITE DEFAULT-CAR))
 (4 2 (:DEFINITION TRUE-LISTP))
 )
(MEMBER-EQUAL-INTERSECTION-EQUAL
 (165 160 (:REWRITE DEFAULT-CAR))
 (129 125 (:REWRITE DEFAULT-CDR))
 )
(SETP-EQUAL-INTERSECTION-EQUAL
 (58 56 (:REWRITE DEFAULT-CDR))
 (51 50 (:REWRITE DEFAULT-CAR))
 )
(MEMBER-EQUAL-SET-DIFFERENCE-EQUAL
 (165 160 (:REWRITE DEFAULT-CAR))
 (129 125 (:REWRITE DEFAULT-CDR))
 )
(SETP-EQUAL-SET-DIFFERENCE-EQUAL
 (58 56 (:REWRITE DEFAULT-CDR))
 (51 50 (:REWRITE DEFAULT-CAR))
 )
(MEMBER-EQUAL-UNION-EQUAL
 (165 160 (:REWRITE DEFAULT-CAR))
 (131 127 (:REWRITE DEFAULT-CDR))
 (64 64 (:TYPE-PRESCRIPTION UNION-EQUAL))
 )
(SETP-EQUAL-UNION-EQUAL
 (158 158 (:REWRITE DEFAULT-CDR))
 (96 96 (:REWRITE DEFAULT-CAR))
 )
(INTERSECTION-EQUAL-NIL
 (5 5 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE DEFAULT-CDR))
 )
(SUBSETP-EQUAL-INTERSECTION-EQUAL-INSTANCE
 (29 29 (:REWRITE DEFAULT-CAR))
 (23 23 (:REWRITE DEFAULT-CDR))
 )
(INTERSECTION-EQUAL-IDENTITY
 (2 1 (:DEFINITION TRUE-LISTP))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(UNION-EQUAL-NIL
 (8 8 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE DEFAULT-CDR))
 )
(SUBSETP-EQUAL-UNION-EQUAL-INSTANCE
 (28 28 (:REWRITE DEFAULT-CAR))
 (26 26 (:REWRITE DEFAULT-CDR))
 (14 7 (:DEFINITION TRUE-LISTP))
 )
(UNION-EQUAL-IDENTITY
 (2 1 (:DEFINITION TRUE-LISTP))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(SET-DIFFERENCE-EQUAL-NIL
 (8 8 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE DEFAULT-CDR))
 )
(SUBSETP-EQUAL-SET-DIFFERENCE-EQUAL-INSTANCE
 (33 33 (:REWRITE DEFAULT-CAR))
 (32 32 (:REWRITE DEFAULT-CDR))
 (16 8 (:DEFINITION TRUE-LISTP))
 )
(SET-DIFFERENCE-EQUAL-IDENTITY
 (2 1 (:DEFINITION TRUE-LISTP))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(SET-DIFFERENCE-EQUAL-CONS
 (189 18 (:REWRITE SUBSETP-EQUAL-SET-DIFFERENCE-EQUAL-INSTANCE))
 (144 27 (:DEFINITION TRUE-LISTP))
 (108 108 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (52 52 (:REWRITE DEFAULT-CDR))
 (37 37 (:REWRITE DEFAULT-CAR))
 )
(SET-DIFFERENCE-NULL-INTERSECTION
 (64 8 (:REWRITE SUBSETP-EQUAL-SET-DIFFERENCE-EQUAL-INSTANCE))
 (57 57 (:REWRITE DEFAULT-CDR))
 (57 57 (:REWRITE DEFAULT-CAR))
 )
(MEMBER-EQUAL-APPEND
 (56 44 (:REWRITE DEFAULT-CAR))
 (48 24 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (40 31 (:REWRITE DEFAULT-CDR))
 (24 24 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (24 24 (:TYPE-PRESCRIPTION BINARY-APPEND))
 )
(NO-DUPLICATESP-EQUAL-APPEND
 (177 150 (:REWRITE DEFAULT-CDR))
 (138 16 (:REWRITE SUBSETP-EQUAL-INTERSECTION-EQUAL-INSTANCE))
 (125 110 (:REWRITE DEFAULT-CAR))
 (113 113 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (94 19 (:DEFINITION TRUE-LISTP))
 (62 31 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (31 31 (:TYPE-PRESCRIPTION BINARY-APPEND))
 )
(TRUE-LISTP-APPEND-REWRITE
 (228 114 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (114 114 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (16 13 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-CAR))
 )
(SETP-EQUAL-APPEND
 (153 9 (:REWRITE SUBSETP-EQUAL-INTERSECTION-EQUAL-INSTANCE))
 (126 9 (:DEFINITION SUBSETP-EQUAL))
 (81 18 (:DEFINITION MEMBER-EQUAL))
 (49 49 (:REWRITE DEFAULT-CDR))
 (45 45 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (40 40 (:REWRITE DEFAULT-CAR))
 (6 3 (:DEFINITION TRUE-LISTP))
 (3 1 (:DEFINITION BINARY-APPEND))
 (2 1 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (1 1 (:TYPE-PRESCRIPTION BINARY-APPEND))
 )
