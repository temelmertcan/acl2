(L0
 (50 50 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE CDR-CONS))
 (2 2 (:REWRITE CAR-CONS))
 )
(SUBSETP-EQUAL-REFLEXIVE
 (16 16 (:REWRITE DEFAULT-CAR))
 )
(HONS-ASSOC-EQUAL-OF-LIST-FIX
 (60 54 (:REWRITE DEFAULT-CAR))
 (20 17 (:REWRITE DEFAULT-CDR))
 )
(HONS-ASSOC-EQUAL-APPEND
 (184 157 (:REWRITE DEFAULT-CAR))
 (81 63 (:REWRITE DEFAULT-CDR))
 (68 34 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (34 34 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (34 34 (:TYPE-PRESCRIPTION BINARY-APPEND))
 )
(ALIST-KEYS-OF-LIST-FIX
 (33 33 (:TYPE-PRESCRIPTION TRUE-LIST-FIX))
 (21 21 (:REWRITE DEFAULT-CDR))
 (19 19 (:REWRITE DEFAULT-CAR))
 )
(ALISTS-AGREE)
(L0
 (119 115 (:REWRITE DEFAULT-CAR))
 (53 52 (:REWRITE DEFAULT-CDR))
 )
(LIST-EQUIV-IMPLIES-EQUAL-ALISTS-AGREE-1
 (64 8 (:DEFINITION HONS-ASSOC-EQUAL))
 (42 42 (:REWRITE DEFAULT-CAR))
 (22 22 (:REWRITE DEFAULT-CDR))
 (8 8 (:DEFINITION HONS-EQUAL))
 )
(ALISTS-AGREE-HONS-ASSOC-EQUAL
 (112 14 (:DEFINITION HONS-ASSOC-EQUAL))
 (71 71 (:REWRITE DEFAULT-CAR))
 (32 32 (:REWRITE DEFAULT-CDR))
 (14 14 (:DEFINITION HONS-EQUAL))
 )
(ALISTS-AGREE-SELF
 (48 6 (:DEFINITION HONS-ASSOC-EQUAL))
 (30 30 (:REWRITE DEFAULT-CAR))
 (14 14 (:REWRITE DEFAULT-CDR))
 (6 6 (:DEFINITION HONS-EQUAL))
 )
(ALISTS-AGREE-SYM
 (110 110 (:REWRITE DEFAULT-CAR))
 (48 48 (:REWRITE DEFAULT-CDR))
 )
(ALISTS-DISAGREE-WITNESS)
(ALISTS-AGREE-IFF-WITNESS
 (391 391 (:REWRITE DEFAULT-CAR))
 (186 186 (:REWRITE DEFAULT-CDR))
 )
(ALISTS-AGREE-TRANS
 (190 190 (:REWRITE DEFAULT-CAR))
 (82 82 (:REWRITE DEFAULT-CDR))
 )
(SUB-ALISTP)
(SUB-ALISTP-SELF
 (1 1 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 )
(SUB-ALISTP-HONS-ASSOC-EQUAL
 (15 15 (:REWRITE DEFAULT-CAR))
 (8 8 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 )
(NOT-SUB-ALISTP-WITNESS)
(SUB-ALISTP-IFF-WITNESS
 (36 36 (:REWRITE DEFAULT-CAR))
 (18 18 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 )
(SUB-ALISTP-WHEN-WITNESS)
(SUB-ALISTP-TRANS
 (192 192 (:REWRITE DEFAULT-CAR))
 (96 96 (:REWRITE DEFAULT-CDR))
 )
(ALIST-EQUIV)
(ALIST-EQUIV-IS-AN-EQUIVALENCE)
(L0
 (24 3 (:DEFINITION HONS-ASSOC-EQUAL))
 (12 12 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE DEFAULT-CDR))
 (3 3 (:DEFINITION HONS-EQUAL))
 )
(ALIST-EQUIV-MEANS-ALL-KEYS-AGREE
 (50 50 (:REWRITE DEFAULT-CAR))
 (22 22 (:REWRITE DEFAULT-CDR))
 )
(L0
 (105 105 (:REWRITE DEFAULT-CAR))
 (49 49 (:REWRITE DEFAULT-CDR))
 (15 5 (:DEFINITION TRUE-LIST-FIX))
 )
(L1
 (105 105 (:REWRITE DEFAULT-CAR))
 (49 49 (:REWRITE DEFAULT-CDR))
 (15 5 (:DEFINITION TRUE-LIST-FIX))
 )
(L2
 (56 2 (:DEFINITION ALISTS-AGREE))
 (36 4 (:DEFINITION HONS-GET))
 (32 4 (:DEFINITION HONS-ASSOC-EQUAL))
 (21 21 (:REWRITE DEFAULT-CAR))
 (11 11 (:REWRITE DEFAULT-CDR))
 (8 8 (:TYPE-PRESCRIPTION HONS-ASSOC-EQUAL))
 (4 4 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-ALIST-KEYS))
 (4 4 (:DEFINITION HONS-EQUAL))
 (3 1 (:DEFINITION TRUE-LIST-FIX))
 (2 2 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 )
(L3
 (56 2 (:DEFINITION ALISTS-AGREE))
 (36 4 (:DEFINITION HONS-GET))
 (32 4 (:DEFINITION HONS-ASSOC-EQUAL))
 (21 21 (:REWRITE DEFAULT-CAR))
 (11 11 (:REWRITE DEFAULT-CDR))
 (8 8 (:TYPE-PRESCRIPTION HONS-ASSOC-EQUAL))
 (4 4 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-ALIST-KEYS))
 (4 4 (:DEFINITION HONS-EQUAL))
 (3 1 (:DEFINITION TRUE-LIST-FIX))
 (2 2 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 )
(LIST-EQUIV-IMPLIES-EQUAL-SUB-ALISTP-1
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 )
(LIST-EQUIV-IMPLIES-EQUAL-SUB-ALISTP-2
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 )
(LIST-EQUIV-REFINES-ALIST-EQUIV)
(ALIST-EQUIV-IMPLIES-EQUAL-HONS-ASSOC-EQUAL-2
 (16 2 (:DEFINITION HONS-ASSOC-EQUAL))
 (10 10 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE DEFAULT-CDR))
 (2 2 (:DEFINITION HONS-EQUAL))
 )
(L0
 (16 16 (:REWRITE DEFAULT-CAR))
 (8 8 (:REWRITE DEFAULT-CDR))
 )
(ALISTS-AGREE-WHEN-AGREE-ON-ALIST-EQUIV-BAD-GUY
 (96 12 (:DEFINITION HONS-ASSOC-EQUAL))
 (52 52 (:REWRITE DEFAULT-CAR))
 (27 27 (:REWRITE DEFAULT-CDR))
 (12 12 (:DEFINITION HONS-EQUAL))
 )
(ALISTS-AGREE-WHEN-AGREE-ON-ALIST-EQUIV-BAD-GUY1
 (96 12 (:DEFINITION HONS-ASSOC-EQUAL))
 (52 52 (:REWRITE DEFAULT-CAR))
 (27 27 (:REWRITE DEFAULT-CDR))
 (12 12 (:DEFINITION HONS-EQUAL))
 )
(SUB-ALISTP-WHEN-AGREE-ON-ALIST-EQUIV-BAD-GUY
 (16 16 (:REWRITE DEFAULT-CAR))
 (8 8 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 )
(SUB-ALISTP-WHEN-AGREE-ON-ALIST-EQUIV-BAD-GUY1
 (32 4 (:DEFINITION HONS-ASSOC-EQUAL))
 (16 16 (:REWRITE DEFAULT-CAR))
 (8 8 (:REWRITE DEFAULT-CDR))
 (4 4 (:DEFINITION HONS-EQUAL))
 (1 1 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 )
(ALIST-EQUIV-WHEN-AGREE-ON-BAD-GUY
 (24 24 (:REWRITE DEFAULT-CAR))
 (12 12 (:REWRITE DEFAULT-CDR))
 )
(ALIST-EQUIV-IFF-AGREE-ON-BAD-GUY
 (32 32 (:REWRITE DEFAULT-CAR))
 (16 16 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE SUB-ALISTP-HONS-ASSOC-EQUAL))
 )
(ALIST-EQUIV-IMPLIES-EQUAL-ALISTS-AGREE-2
 (100 100 (:REWRITE DEFAULT-CAR))
 (44 44 (:REWRITE DEFAULT-CDR))
 )
(ALIST-EQUIV-IMPLIES-EQUAL-ALISTS-AGREE-3
 (100 100 (:REWRITE DEFAULT-CAR))
 (44 44 (:REWRITE DEFAULT-CDR))
 )
(ALIST-EQUIV-IMPLIES-EQUAL-SUB-ALISTP-1)
(ALIST-EQUIV-IMPLIES-EQUAL-SUB-ALISTP-2)
(L0
 (51 48 (:REWRITE DEFAULT-CAR))
 (24 21 (:REWRITE DEFAULT-CDR))
 (10 10 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 )
(L1
 (124 123 (:REWRITE DEFAULT-CAR))
 (80 79 (:REWRITE DEFAULT-CDR))
 )
(L2
 (149 148 (:REWRITE DEFAULT-CAR))
 (91 90 (:REWRITE DEFAULT-CDR))
 )
(SET-EQUIV-IMPLIES-SET-EQUIV-ALIST-KEYS-1
 (16 2 (:DEFINITION ALIST-KEYS))
 (14 2 (:DEFINITION SUBSETP-EQUAL))
 (10 10 (:REWRITE DEFAULT-CAR))
 (8 8 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 (6 2 (:DEFINITION MEMBER-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 )
(L0
 (44 41 (:REWRITE DEFAULT-CAR))
 (33 30 (:REWRITE DEFAULT-CDR))
 (10 10 (:REWRITE ALIST-VALS-WHEN-ATOM))
 )
(L1
 (107 106 (:REWRITE DEFAULT-CDR))
 (97 96 (:REWRITE DEFAULT-CAR))
 )
(L2
 (122 121 (:REWRITE DEFAULT-CDR))
 (118 117 (:REWRITE DEFAULT-CAR))
 )
(SET-EQUIV-IMPLIES-SET-EQUIV-ALIST-VALS-1
 (16 2 (:DEFINITION ALIST-VALS))
 (14 2 (:DEFINITION SUBSETP-EQUAL))
 (10 10 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE ALIST-VALS-WHEN-ATOM))
 (6 2 (:DEFINITION MEMBER-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 )
(L1
 (40 40 (:REWRITE DEFAULT-CAR))
 (26 26 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 )
(L2)
(ALIST-EQUIV-IMPLIES-SET-EQUIV-ALIST-KEYS-1
 (2 2 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 )
(ALIST-EQUIV-IMPLIES-ALIST-EQUIV-CONS-2
 (34 34 (:REWRITE DEFAULT-CAR))
 (16 16 (:REWRITE DEFAULT-CDR))
 )
(ALIST-EQUIV-IMPLIES-ALIST-EQUIV-APPEND-1
 (64 8 (:DEFINITION HONS-ASSOC-EQUAL))
 (34 34 (:REWRITE DEFAULT-CAR))
 (18 18 (:REWRITE DEFAULT-CDR))
 (12 6 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (8 8 (:DEFINITION HONS-EQUAL))
 (6 6 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (6 6 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (6 2 (:DEFINITION BINARY-APPEND))
 )
(ALIST-EQUIV-IMPLIES-ALIST-EQUIV-APPEND-2
 (64 8 (:DEFINITION HONS-ASSOC-EQUAL))
 (34 34 (:REWRITE DEFAULT-CAR))
 (18 18 (:REWRITE DEFAULT-CDR))
 (12 6 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (8 8 (:DEFINITION HONS-EQUAL))
 (6 6 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (6 6 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (6 2 (:DEFINITION BINARY-APPEND))
 )
