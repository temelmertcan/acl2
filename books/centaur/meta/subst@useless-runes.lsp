(TMP-DEFTYPES-PSEUDO-VAR-P-OF-PSEUDO-VAR-FIX)
(CMR::PSEUDO-TERM-SUBST-P)
(CMR::BOOLEANP-OF-PSEUDO-VAR-P-FOR-PSEUDO-TERM-SUBST-P-KEY-LEMMA)
(CMR::BOOLEANP-OF-PSEUDO-TERMP-FOR-PSEUDO-TERM-SUBST-P-VAL-LEMMA)
(CMR::BOOLEANP-OF-PSEUDO-VAR-P-FOR-PSEUDO-TERM-SUBST-P-KEY)
(CMR::BOOLEANP-OF-PSEUDO-TERMP-FOR-PSEUDO-TERM-SUBST-P-VAL)
(CMR::TRUE-LISTP-WHEN-PSEUDO-TERM-SUBST-P)
(CMR::PSEUDO-TERM-SUBST-P-WHEN-NOT-CONSP)
(CMR::PSEUDO-TERM-SUBST-P-OF-CDR-WHEN-PSEUDO-TERM-SUBST-P)
(CMR::PSEUDO-TERM-SUBST-P-OF-CONS)
(CMR::PSEUDO-TERM-SUBST-P-OF-PUT-ASSOC
     (56 10
         (:REWRITE CMR::PSEUDO-TERM-SUBST-P-OF-CDR-WHEN-PSEUDO-TERM-SUBST-P))
     (16 16
         (:REWRITE CMR::PSEUDO-TERM-SUBST-P-WHEN-NOT-CONSP)))
(CMR::PSEUDO-TERM-SUBST-P-OF-HONS-SHRINK-ALIST)
(CMR::PSEUDO-TERM-SUBST-P-OF-HONS-ACONS)
(CMR::PSEUDO-TERMP-OF-CDR-OF-HONS-ASSOC-EQUAL-WHEN-PSEUDO-TERM-SUBST-P)
(CMR::ALISTP-WHEN-PSEUDO-TERM-SUBST-P)
(CMR::PSEUDO-TERMP-OF-CDAR-WHEN-PSEUDO-TERM-SUBST-P)
(CMR::PSEUDO-VAR-P-OF-CAAR-WHEN-PSEUDO-TERM-SUBST-P)
(CMR::PSEUDO-TERM-SUBST-FIX$INLINE)
(CMR::PSEUDO-TERM-SUBST-P-OF-PSEUDO-TERM-SUBST-FIX
     (689 6
          (:REWRITE PSEUDO-TERM-FIX-WHEN-PSEUDO-TERMP))
     (620 4 (:DEFINITION PSEUDO-TERMP))
     (148 148 (:TYPE-PRESCRIPTION LEN))
     (144 20 (:REWRITE FTY::EQUAL-OF-LEN))
     (140 28 (:DEFINITION LEN))
     (100 17
          (:REWRITE CMR::PSEUDO-VAR-P-OF-CAAR-WHEN-PSEUDO-TERM-SUBST-P))
     (100 12 (:DEFINITION LENGTH))
     (98 98 (:REWRITE DEFAULT-CDR))
     (82 9
         (:DEFINITION CMR::PSEUDO-TERM-SUBST-P))
     (80 80 (:REWRITE DEFAULT-CAR))
     (80 16
         (:REWRITE PSEUDO-TERM-LISTP-CDR-WHEN-PSEUDO-TERM-LISTP))
     (78 36
         (:REWRITE CMR::PSEUDO-TERM-SUBST-P-WHEN-NOT-CONSP))
     (72 72
         (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
     (60 4
         (:REWRITE PSEUDO-TERMP-CAR-WHEN-PSEUDO-TERM-LISTP))
     (56 28 (:REWRITE DEFAULT-+-2))
     (55 12
         (:REWRITE CMR::PSEUDO-TERMP-OF-CDAR-WHEN-PSEUDO-TERM-SUBST-P))
     (40 40 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
     (40 8 (:DEFINITION TRUE-LISTP))
     (32 32 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (28 28 (:REWRITE DEFAULT-+-1))
     (24 24
         (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
     (24 10
         (:REWRITE CMR::PSEUDO-TERM-SUBST-P-OF-CDR-WHEN-PSEUDO-TERM-SUBST-P))
     (24 4 (:DEFINITION SYMBOL-LISTP))
     (20 20 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
     (8 8 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
     (4 4 (:REWRITE DEFAULT-COERCE-2))
     (4 4 (:REWRITE DEFAULT-COERCE-1)))
(CMR::PSEUDO-TERM-SUBST-FIX-WHEN-PSEUDO-TERM-SUBST-P
    (2425 17 (:DEFINITION PSEUDO-TERMP))
    (1082 31
          (:REWRITE CMR::PSEUDO-TERMP-OF-CDAR-WHEN-PSEUDO-TERM-SUBST-P))
    (608 28
         (:REWRITE CMR::PSEUDO-TERM-SUBST-P-OF-CDR-WHEN-PSEUDO-TERM-SUBST-P))
    (595 119 (:DEFINITION LEN))
    (567 85 (:REWRITE FTY::EQUAL-OF-LEN))
    (514 514 (:TYPE-PRESCRIPTION LEN))
    (425 51 (:DEFINITION LENGTH))
    (414 410 (:REWRITE DEFAULT-CDR))
    (330 66
         (:REWRITE PSEUDO-TERM-LISTP-CDR-WHEN-PSEUDO-TERM-LISTP))
    (290 290
         (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
    (286 282 (:REWRITE DEFAULT-CAR))
    (255 17
         (:REWRITE PSEUDO-TERMP-CAR-WHEN-PSEUDO-TERM-LISTP))
    (238 119 (:REWRITE DEFAULT-+-2))
    (140 34 (:DEFINITION TRUE-LISTP))
    (119 119 (:REWRITE DEFAULT-+-1))
    (100 100
         (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
    (96 96 (:TYPE-PRESCRIPTION TRUE-LISTP))
    (87 17 (:DEFINITION SYMBOL-LISTP))
    (65 65 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
    (34 34
        (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
    (17 17 (:REWRITE DEFAULT-COERCE-2))
    (17 17 (:REWRITE DEFAULT-COERCE-1)))
(CMR::PSEUDO-TERM-SUBST-FIX$INLINE
     (7 7
        (:REWRITE CMR::PSEUDO-TERM-SUBST-P-WHEN-NOT-CONSP))
     (6 2
        (:REWRITE CMR::PSEUDO-TERMP-OF-CDAR-WHEN-PSEUDO-TERM-SUBST-P))
     (6 2
        (:REWRITE CMR::PSEUDO-TERM-SUBST-P-OF-CDR-WHEN-PSEUDO-TERM-SUBST-P)))
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT
     (1 1
        (:REWRITE CMR::PSEUDO-TERM-SUBST-P-WHEN-NOT-CONSP)))
(CMR::PSEUDO-TERM-SUBST-EQUIV$INLINE)
(CMR::PSEUDO-TERM-SUBST-EQUIV-IS-AN-EQUIVALENCE)
(CMR::PSEUDO-TERM-SUBST-EQUIV-IMPLIES-EQUAL-PSEUDO-TERM-SUBST-FIX-1)
(CMR::PSEUDO-TERM-SUBST-FIX-UNDER-PSEUDO-TERM-SUBST-EQUIV)
(CMR::EQUAL-OF-PSEUDO-TERM-SUBST-FIX-1-FORWARD-TO-PSEUDO-TERM-SUBST-EQUIV)
(CMR::EQUAL-OF-PSEUDO-TERM-SUBST-FIX-2-FORWARD-TO-PSEUDO-TERM-SUBST-EQUIV)
(CMR::PSEUDO-TERM-SUBST-EQUIV-OF-PSEUDO-TERM-SUBST-FIX-1-FORWARD)
(CMR::PSEUDO-TERM-SUBST-EQUIV-OF-PSEUDO-TERM-SUBST-FIX-2-FORWARD)
(CMR::CONS-OF-PSEUDO-TERM-FIX-V-UNDER-PSEUDO-TERM-SUBST-EQUIV
     (31 4
         (:REWRITE CMR::PSEUDO-TERM-SUBST-FIX-WHEN-PSEUDO-TERM-SUBST-P))
     (22 2
         (:REWRITE CMR::PSEUDO-TERM-SUBST-P-OF-CONS))
     (6 6
        (:TYPE-PRESCRIPTION CMR::PSEUDO-TERM-SUBST-P))
     (3 3
        (:REWRITE CMR::PSEUDO-TERM-SUBST-P-WHEN-NOT-CONSP)))
(CMR::CONS-OF-PSEUDO-TERM-FIX-V-NORMALIZE-CONST-UNDER-PSEUDO-TERM-SUBST-EQUIV)
(CMR::CONS-PSEUDO-TERM-EQUIV-CONGRUENCE-ON-V-UNDER-PSEUDO-TERM-SUBST-EQUIV)
(CMR::CONS-OF-PSEUDO-TERM-SUBST-FIX-Y-UNDER-PSEUDO-TERM-SUBST-EQUIV
     (18 2
         (:REWRITE CMR::PSEUDO-TERM-SUBST-P-OF-CONS))
     (9 9 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
     (6 2
        (:REWRITE PSEUDO-TERM-FIX-WHEN-PSEUDO-TERMP))
     (2 2
        (:REWRITE CMR::PSEUDO-TERM-SUBST-P-WHEN-NOT-CONSP)))
(CMR::CONS-OF-PSEUDO-TERM-SUBST-FIX-Y-NORMALIZE-CONST-UNDER-PSEUDO-TERM-SUBST-EQUIV)
(CMR::CONS-PSEUDO-TERM-SUBST-EQUIV-CONGRUENCE-ON-Y-UNDER-PSEUDO-TERM-SUBST-EQUIV)
(CMR::PSEUDO-TERM-SUBST-FIX-OF-ACONS
 (17 3
     (:REWRITE CMR::PSEUDO-TERM-SUBST-FIX-WHEN-PSEUDO-TERM-SUBST-P))
 (10 1
     (:REWRITE CMR::PSEUDO-TERM-SUBST-P-OF-CONS))
 (6 6 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
 (6 2
    (:REWRITE PSEUDO-TERM-FIX-WHEN-PSEUDO-TERMP))
 (4 4
    (:TYPE-PRESCRIPTION CMR::PSEUDO-TERM-SUBST-P))
 (2 2
    (:REWRITE CMR::PSEUDO-TERM-SUBST-P-WHEN-NOT-CONSP))
 (1
  1
  (:REWRITE
   CMR::CONS-OF-PSEUDO-TERM-SUBST-FIX-Y-NORMALIZE-CONST-UNDER-PSEUDO-TERM-SUBST-EQUIV))
 (1
  1
  (:REWRITE
   CMR::CONS-OF-PSEUDO-TERM-FIX-V-NORMALIZE-CONST-UNDER-PSEUDO-TERM-SUBST-EQUIV)))
(CMR::HONS-ASSOC-EQUAL-OF-PSEUDO-TERM-SUBST-FIX
 (255 34
      (:REWRITE CMR::PSEUDO-TERM-SUBST-FIX-WHEN-PSEUDO-TERM-SUBST-P))
 (225 36
      (:REWRITE PSEUDO-TERM-FIX-WHEN-PSEUDO-TERMP))
 (131 38
      (:REWRITE CMR::PSEUDO-TERM-SUBST-P-OF-CDR-WHEN-PSEUDO-TERM-SUBST-P))
 (116 116
      (:REWRITE CMR::PSEUDO-TERM-SUBST-P-WHEN-NOT-CONSP))
 (88 22
     (:REWRITE CMR::PSEUDO-VAR-P-OF-CAAR-WHEN-PSEUDO-TERM-SUBST-P))
 (84 21
     (:REWRITE CMR::PSEUDO-TERMP-OF-CDAR-WHEN-PSEUDO-TERM-SUBST-P))
 (62 62 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
 (43
  8
  (:REWRITE
     CMR::PSEUDO-TERMP-OF-CDR-OF-HONS-ASSOC-EQUAL-WHEN-PSEUDO-TERM-SUBST-P)))
(CMR::PSEUDO-TERM-SUBST-FIX-OF-APPEND
 (122 17
      (:REWRITE CMR::PSEUDO-TERM-SUBST-FIX-WHEN-PSEUDO-TERM-SUBST-P))
 (55 55
     (:TYPE-PRESCRIPTION CMR::PSEUDO-TERM-SUBST-P))
 (40 28
     (:REWRITE CMR::PSEUDO-TERM-SUBST-P-WHEN-NOT-CONSP))
 (22 4
     (:REWRITE PSEUDO-TERM-FIX-WHEN-PSEUDO-TERMP))
 (21 1
     (:REWRITE CMR::PSEUDO-TERM-SUBST-P-OF-CONS))
 (16 4
     (:REWRITE CMR::PSEUDO-VAR-P-OF-CAAR-WHEN-PSEUDO-TERM-SUBST-P))
 (16 4
     (:REWRITE CMR::PSEUDO-TERMP-OF-CDAR-WHEN-PSEUDO-TERM-SUBST-P))
 (16 4
     (:REWRITE CMR::PSEUDO-TERM-SUBST-P-OF-CDR-WHEN-PSEUDO-TERM-SUBST-P))
 (8 8 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
 (1
  1
  (:REWRITE
   CMR::CONS-OF-PSEUDO-TERM-SUBST-FIX-Y-NORMALIZE-CONST-UNDER-PSEUDO-TERM-SUBST-EQUIV)))
(CMR::CONSP-CAR-OF-PSEUDO-TERM-SUBST-FIX
     (27 8
         (:REWRITE CMR::PSEUDO-TERM-SUBST-FIX-WHEN-PSEUDO-TERM-SUBST-P))
     (19 19
         (:TYPE-PRESCRIPTION CMR::PSEUDO-TERM-SUBST-P))
     (14 2
         (:REWRITE PSEUDO-TERM-FIX-WHEN-PSEUDO-TERMP))
     (10 10
         (:REWRITE CMR::PSEUDO-TERM-SUBST-P-WHEN-NOT-CONSP))
     (8 2
        (:REWRITE CMR::PSEUDO-VAR-P-OF-CAAR-WHEN-PSEUDO-TERM-SUBST-P))
     (8 2
        (:REWRITE CMR::PSEUDO-TERMP-OF-CDAR-WHEN-PSEUDO-TERM-SUBST-P))
     (8 2
        (:REWRITE CMR::PSEUDO-TERM-SUBST-P-OF-CDR-WHEN-PSEUDO-TERM-SUBST-P))
     (4 4 (:TYPE-PRESCRIPTION PSEUDO-TERMP)))
(TMP-DEFTYPES-PSEUDO-VAR-P-OF-PSEUDO-VAR-FIX)
(CMR::PSEUDO-VAR-LIST-P)
(STD::DEFLIST-LOCAL-BOOLEANP-ELEMENT-THM)
(CMR::PSEUDO-VAR-LIST-P-OF-CONS)
(CMR::PSEUDO-VAR-LIST-P-OF-CDR-WHEN-PSEUDO-VAR-LIST-P)
(CMR::PSEUDO-VAR-LIST-P-WHEN-NOT-CONSP)
(CMR::PSEUDO-VAR-P-OF-CAR-WHEN-PSEUDO-VAR-LIST-P)
(CMR::TRUE-LISTP-WHEN-PSEUDO-VAR-LIST-P)
(CMR::PSEUDO-VAR-LIST-FIX$INLINE)
(CMR::PSEUDO-VAR-LIST-P-OF-PSEUDO-VAR-LIST-FIX
     (15 1
         (:REWRITE PSEUDO-VAR-FIX-WHEN-PSEUDO-VAR-P))
     (12 2
         (:REWRITE CMR::PSEUDO-VAR-P-OF-CAR-WHEN-PSEUDO-VAR-LIST-P))
     (9 5
        (:REWRITE CMR::PSEUDO-VAR-LIST-P-WHEN-NOT-CONSP))
     (9 1 (:DEFINITION CMR::PSEUDO-VAR-LIST-P))
     (4 4 (:TYPE-PRESCRIPTION PSEUDO-VAR-P))
     (2 1
        (:REWRITE CMR::PSEUDO-VAR-LIST-P-OF-CDR-WHEN-PSEUDO-VAR-LIST-P)))
(CMR::PSEUDO-VAR-LIST-FIX-WHEN-PSEUDO-VAR-LIST-P
     (17 4
         (:REWRITE CMR::PSEUDO-VAR-LIST-P-OF-CDR-WHEN-PSEUDO-VAR-LIST-P))
     (9 3
        (:REWRITE CMR::PSEUDO-VAR-P-OF-CAR-WHEN-PSEUDO-VAR-LIST-P)))
(CMR::PSEUDO-VAR-LIST-FIX$INLINE
     (4 4
        (:REWRITE CMR::PSEUDO-VAR-LIST-P-WHEN-NOT-CONSP))
     (4 1
        (:REWRITE CMR::PSEUDO-VAR-P-OF-CAR-WHEN-PSEUDO-VAR-LIST-P))
     (4 1
        (:REWRITE CMR::PSEUDO-VAR-LIST-P-OF-CDR-WHEN-PSEUDO-VAR-LIST-P)))
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT
     (1 1
        (:REWRITE CMR::PSEUDO-VAR-LIST-P-WHEN-NOT-CONSP)))
(CMR::PSEUDO-VAR-LIST-EQUIV$INLINE)
(CMR::PSEUDO-VAR-LIST-EQUIV-IS-AN-EQUIVALENCE)
(CMR::PSEUDO-VAR-LIST-EQUIV-IMPLIES-EQUAL-PSEUDO-VAR-LIST-FIX-1)
(CMR::PSEUDO-VAR-LIST-FIX-UNDER-PSEUDO-VAR-LIST-EQUIV)
(CMR::EQUAL-OF-PSEUDO-VAR-LIST-FIX-1-FORWARD-TO-PSEUDO-VAR-LIST-EQUIV)
(CMR::EQUAL-OF-PSEUDO-VAR-LIST-FIX-2-FORWARD-TO-PSEUDO-VAR-LIST-EQUIV)
(CMR::PSEUDO-VAR-LIST-EQUIV-OF-PSEUDO-VAR-LIST-FIX-1-FORWARD)
(CMR::PSEUDO-VAR-LIST-EQUIV-OF-PSEUDO-VAR-LIST-FIX-2-FORWARD)
(CMR::CAR-OF-PSEUDO-VAR-LIST-FIX-X-UNDER-PSEUDO-VAR-EQUIV
     (21 3
         (:REWRITE PSEUDO-VAR-FIX-WHEN-PSEUDO-VAR-P))
     (12 12
         (:TYPE-PRESCRIPTION CMR::PSEUDO-VAR-LIST-P))
     (12 3
         (:REWRITE CMR::PSEUDO-VAR-P-OF-CAR-WHEN-PSEUDO-VAR-LIST-P))
     (12 2
         (:REWRITE CMR::PSEUDO-VAR-LIST-FIX-WHEN-PSEUDO-VAR-LIST-P))
     (6 6 (:TYPE-PRESCRIPTION PSEUDO-VAR-P))
     (6 6
        (:REWRITE CMR::PSEUDO-VAR-LIST-P-WHEN-NOT-CONSP))
     (4 1
        (:REWRITE CMR::PSEUDO-VAR-LIST-P-OF-CDR-WHEN-PSEUDO-VAR-LIST-P))
     (3 3
        (:TYPE-PRESCRIPTION CMR::PSEUDO-VAR-LIST-FIX$INLINE)))
(CMR::CAR-OF-PSEUDO-VAR-LIST-FIX-X-NORMALIZE-CONST-UNDER-PSEUDO-VAR-EQUIV)
(CMR::CAR-PSEUDO-VAR-LIST-EQUIV-CONGRUENCE-ON-X-UNDER-PSEUDO-VAR-EQUIV)
(CMR::CDR-OF-PSEUDO-VAR-LIST-FIX-X-UNDER-PSEUDO-VAR-LIST-EQUIV
     (29 3
         (:REWRITE CMR::PSEUDO-VAR-LIST-P-OF-CDR-WHEN-PSEUDO-VAR-LIST-P))
     (14 2
         (:REWRITE PSEUDO-VAR-FIX-WHEN-PSEUDO-VAR-P))
     (8 2
        (:REWRITE CMR::PSEUDO-VAR-P-OF-CAR-WHEN-PSEUDO-VAR-LIST-P))
     (4 4 (:TYPE-PRESCRIPTION PSEUDO-VAR-P)))
(CMR::CDR-OF-PSEUDO-VAR-LIST-FIX-X-NORMALIZE-CONST-UNDER-PSEUDO-VAR-LIST-EQUIV)
(CMR::CDR-PSEUDO-VAR-LIST-EQUIV-CONGRUENCE-ON-X-UNDER-PSEUDO-VAR-LIST-EQUIV)
(CMR::CONS-OF-PSEUDO-VAR-FIX-X-UNDER-PSEUDO-VAR-LIST-EQUIV
 (20 4
     (:REWRITE CMR::PSEUDO-VAR-LIST-FIX-WHEN-PSEUDO-VAR-LIST-P))
 (9 2
    (:REWRITE CMR::PSEUDO-VAR-LIST-P-OF-CONS))
 (6 6
    (:TYPE-PRESCRIPTION CMR::PSEUDO-VAR-LIST-P))
 (5 5
    (:REWRITE CMR::PSEUDO-VAR-LIST-P-WHEN-NOT-CONSP))
 (2
  2
  (:REWRITE
   CMR::CDR-OF-PSEUDO-VAR-LIST-FIX-X-NORMALIZE-CONST-UNDER-PSEUDO-VAR-LIST-EQUIV)))
(CMR::CONS-OF-PSEUDO-VAR-FIX-X-NORMALIZE-CONST-UNDER-PSEUDO-VAR-LIST-EQUIV)
(CMR::CONS-PSEUDO-VAR-EQUIV-CONGRUENCE-ON-X-UNDER-PSEUDO-VAR-LIST-EQUIV)
(CMR::CONS-OF-PSEUDO-VAR-LIST-FIX-Y-UNDER-PSEUDO-VAR-LIST-EQUIV
 (12 2
     (:REWRITE CMR::PSEUDO-VAR-LIST-P-OF-CONS))
 (8 8 (:TYPE-PRESCRIPTION PSEUDO-VAR-P))
 (5 4
    (:REWRITE CMR::PSEUDO-VAR-LIST-P-WHEN-NOT-CONSP))
 (4 2
    (:REWRITE PSEUDO-VAR-FIX-WHEN-PSEUDO-VAR-P))
 (2
  2
  (:REWRITE
   CMR::CONS-OF-PSEUDO-VAR-FIX-X-NORMALIZE-CONST-UNDER-PSEUDO-VAR-LIST-EQUIV))
 (2
  2
  (:REWRITE
   CMR::CDR-OF-PSEUDO-VAR-LIST-FIX-X-NORMALIZE-CONST-UNDER-PSEUDO-VAR-LIST-EQUIV)))
(CMR::CONS-OF-PSEUDO-VAR-LIST-FIX-Y-NORMALIZE-CONST-UNDER-PSEUDO-VAR-LIST-EQUIV)
(CMR::CONS-PSEUDO-VAR-LIST-EQUIV-CONGRUENCE-ON-Y-UNDER-PSEUDO-VAR-LIST-EQUIV)
(CMR::CONSP-OF-PSEUDO-VAR-LIST-FIX
 (12 2
     (:REWRITE CMR::PSEUDO-VAR-LIST-FIX-WHEN-PSEUDO-VAR-LIST-P))
 (8 8
    (:TYPE-PRESCRIPTION CMR::PSEUDO-VAR-LIST-P))
 (7 1
    (:REWRITE PSEUDO-VAR-FIX-WHEN-PSEUDO-VAR-P))
 (4 4
    (:REWRITE CMR::PSEUDO-VAR-LIST-P-WHEN-NOT-CONSP))
 (4 1
    (:REWRITE CMR::PSEUDO-VAR-P-OF-CAR-WHEN-PSEUDO-VAR-LIST-P))
 (4 1
    (:REWRITE CMR::PSEUDO-VAR-LIST-P-OF-CDR-WHEN-PSEUDO-VAR-LIST-P))
 (2 2 (:TYPE-PRESCRIPTION PSEUDO-VAR-P))
 (1
  1
  (:REWRITE
   CMR::CDR-OF-PSEUDO-VAR-LIST-FIX-X-NORMALIZE-CONST-UNDER-PSEUDO-VAR-LIST-EQUIV)))
(CMR::PSEUDO-VAR-LIST-FIX-UNDER-IFF
 (12 2
     (:REWRITE CMR::PSEUDO-VAR-LIST-FIX-WHEN-PSEUDO-VAR-LIST-P))
 (8 8
    (:TYPE-PRESCRIPTION CMR::PSEUDO-VAR-LIST-P))
 (7 1
    (:REWRITE PSEUDO-VAR-FIX-WHEN-PSEUDO-VAR-P))
 (4 4
    (:REWRITE CMR::PSEUDO-VAR-LIST-P-WHEN-NOT-CONSP))
 (4 1
    (:REWRITE CMR::PSEUDO-VAR-P-OF-CAR-WHEN-PSEUDO-VAR-LIST-P))
 (4 1
    (:REWRITE CMR::PSEUDO-VAR-LIST-P-OF-CDR-WHEN-PSEUDO-VAR-LIST-P))
 (2 2 (:TYPE-PRESCRIPTION PSEUDO-VAR-P))
 (1
  1
  (:REWRITE
   CMR::CDR-OF-PSEUDO-VAR-LIST-FIX-X-NORMALIZE-CONST-UNDER-PSEUDO-VAR-LIST-EQUIV)))
(CMR::PSEUDO-VAR-LIST-FIX-OF-CONS
 (13 3
     (:REWRITE CMR::PSEUDO-VAR-LIST-FIX-WHEN-PSEUDO-VAR-LIST-P))
 (5 1
    (:REWRITE CMR::PSEUDO-VAR-LIST-P-OF-CONS))
 (4 4 (:TYPE-PRESCRIPTION PSEUDO-VAR-P))
 (4 4
    (:TYPE-PRESCRIPTION CMR::PSEUDO-VAR-LIST-P))
 (4 2
    (:REWRITE PSEUDO-VAR-FIX-WHEN-PSEUDO-VAR-P))
 (3 3
    (:REWRITE CMR::PSEUDO-VAR-LIST-P-WHEN-NOT-CONSP))
 (1
  1
  (:REWRITE
   CMR::CONS-OF-PSEUDO-VAR-LIST-FIX-Y-NORMALIZE-CONST-UNDER-PSEUDO-VAR-LIST-EQUIV))
 (1
  1
  (:REWRITE
   CMR::CONS-OF-PSEUDO-VAR-FIX-X-NORMALIZE-CONST-UNDER-PSEUDO-VAR-LIST-EQUIV))
 (1
  1
  (:REWRITE
   CMR::CDR-OF-PSEUDO-VAR-LIST-FIX-X-NORMALIZE-CONST-UNDER-PSEUDO-VAR-LIST-EQUIV)))
(CMR::LEN-OF-PSEUDO-VAR-LIST-FIX
 (23 4
     (:REWRITE CMR::PSEUDO-VAR-LIST-FIX-WHEN-PSEUDO-VAR-LIST-P))
 (13 13
     (:TYPE-PRESCRIPTION CMR::PSEUDO-VAR-LIST-P))
 (8 2
    (:REWRITE CMR::PSEUDO-VAR-LIST-P-OF-CDR-WHEN-PSEUDO-VAR-LIST-P))
 (7 7
    (:REWRITE CMR::PSEUDO-VAR-LIST-P-WHEN-NOT-CONSP))
 (7 1
    (:REWRITE PSEUDO-VAR-FIX-WHEN-PSEUDO-VAR-P))
 (4 1
    (:REWRITE CMR::PSEUDO-VAR-P-OF-CAR-WHEN-PSEUDO-VAR-LIST-P))
 (2 2 (:TYPE-PRESCRIPTION PSEUDO-VAR-P))
 (2
  2
  (:REWRITE
   CMR::CDR-OF-PSEUDO-VAR-LIST-FIX-X-NORMALIZE-CONST-UNDER-PSEUDO-VAR-LIST-EQUIV))
 (1 1 (:REWRITE FTY::EQUAL-OF-LEN)))
(CMR::PSEUDO-VAR-LIST-FIX-OF-APPEND
 (56 10
     (:REWRITE CMR::PSEUDO-VAR-LIST-FIX-WHEN-PSEUDO-VAR-LIST-P))
 (23 23
     (:TYPE-PRESCRIPTION CMR::PSEUDO-VAR-LIST-P))
 (18 12
     (:REWRITE CMR::PSEUDO-VAR-LIST-P-WHEN-NOT-CONSP))
 (8 2
    (:REWRITE CMR::PSEUDO-VAR-LIST-P-OF-CDR-WHEN-PSEUDO-VAR-LIST-P))
 (8 2
    (:REWRITE PSEUDO-VAR-FIX-WHEN-PSEUDO-VAR-P))
 (4 1
    (:REWRITE CMR::PSEUDO-VAR-P-OF-CAR-WHEN-PSEUDO-VAR-LIST-P))
 (2 2 (:TYPE-PRESCRIPTION PSEUDO-VAR-P))
 (2
  2
  (:REWRITE
   CMR::CDR-OF-PSEUDO-VAR-LIST-FIX-X-NORMALIZE-CONST-UNDER-PSEUDO-VAR-LIST-EQUIV))
 (1
  1
  (:REWRITE
   CMR::CONS-OF-PSEUDO-VAR-LIST-FIX-Y-NORMALIZE-CONST-UNDER-PSEUDO-VAR-LIST-EQUIV))
 (1
  1
  (:REWRITE
   CMR::CONS-OF-PSEUDO-VAR-FIX-X-NORMALIZE-CONST-UNDER-PSEUDO-VAR-LIST-EQUIV))
 (1
  1
  (:REWRITE
   CMR::CAR-OF-PSEUDO-VAR-LIST-FIX-X-NORMALIZE-CONST-UNDER-PSEUDO-VAR-EQUIV)))
(CMR::PSEUDO-TERM-SUBST-P-OF-PAIR-VARS
     (96 6 (:DEFINITION PSEUDO-TERM-LISTP))
     (30 6
         (:REWRITE PSEUDO-TERM-LISTP-CDR-WHEN-PSEUDO-TERM-LISTP))
     (27 8
         (:REWRITE CMR::PSEUDO-TERM-SUBST-P-WHEN-NOT-CONSP))
     (26 26 (:REWRITE DEFAULT-CAR))
     (24 24
         (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
     (19 19 (:REWRITE DEFAULT-CDR))
     (6 6 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
     (6 6
        (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP)))
(CMR::PSEUDO-TERM-SUBST-P-OF-PAIRLIS$
     (64 4 (:DEFINITION PSEUDO-TERM-LISTP))
     (20 4
         (:REWRITE PSEUDO-TERM-LISTP-CDR-WHEN-PSEUDO-TERM-LISTP))
     (16 16
         (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
     (15 4
         (:REWRITE CMR::PSEUDO-TERM-SUBST-P-WHEN-NOT-CONSP))
     (11 11 (:REWRITE DEFAULT-CAR))
     (10 10 (:REWRITE DEFAULT-CDR))
     (4 4 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
     (4 4
        (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP)))
(CMR::PSEUDO-TERM-LIST-P-WHEN-PSEUDO-VAR-LIST-P
     (27 6
         (:REWRITE PSEUDO-TERMP-CAR-WHEN-PSEUDO-TERM-LISTP))
     (23 7
         (:REWRITE PSEUDO-TERM-LISTP-CDR-WHEN-PSEUDO-TERM-LISTP))
     (17 17
         (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
     (14 14 (:REWRITE DEFAULT-CAR))
     (10 2
         (:REWRITE CMR::PSEUDO-VAR-LIST-P-OF-CDR-WHEN-PSEUDO-VAR-LIST-P))
     (7 7 (:REWRITE DEFAULT-CDR))
     (6 6
        (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP)))
(CMR::PSEUDO-TERMP-OF-LOOKUP-IN-PSEUDO-TERM-SUBST
     (232 24
          (:REWRITE CMR::PSEUDO-TERM-LIST-P-WHEN-PSEUDO-VAR-LIST-P))
     (184 4
          (:REWRITE PSEUDO-TERMP-CAR-WHEN-PSEUDO-TERM-LISTP))
     (152 16
          (:REWRITE PSEUDO-TERM-LISTP-CDR-WHEN-PSEUDO-TERM-LISTP))
     (136 24
          (:REWRITE CMR::PSEUDO-VAR-LIST-P-OF-CDR-WHEN-PSEUDO-VAR-LIST-P))
     (101 101 (:REWRITE DEFAULT-CAR))
     (96 96 (:REWRITE DEFAULT-CDR))
     (80 16 (:DEFINITION LEN))
     (40 40
         (:REWRITE CMR::PSEUDO-VAR-LIST-P-WHEN-NOT-CONSP))
     (32 16 (:REWRITE DEFAULT-+-2))
     (24 24
         (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
     (16 16 (:REWRITE DEFAULT-+-1))
     (16 8 (:DEFINITION TRUE-LISTP))
     (12 4 (:DEFINITION SYMBOL-LISTP))
     (8 8 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
     (4 4 (:REWRITE DEFAULT-COERCE-2))
     (4 4 (:REWRITE DEFAULT-COERCE-1)))
(CMR::ASSOC-OF-PSEUDO-TERM-SUBST-FIX
    (12948 71
           (:REWRITE PSEUDO-TERM-FIX-WHEN-PSEUDO-TERMP))
    (12274 70 (:DEFINITION PSEUDO-TERMP))
    (5306 35
          (:REWRITE CMR::CONSP-CAR-OF-PSEUDO-TERM-SUBST-FIX))
    (3804 420
          (:REWRITE CMR::PSEUDO-TERM-LIST-P-WHEN-PSEUDO-VAR-LIST-P))
    (3092 70
          (:REWRITE PSEUDO-TERMP-CAR-WHEN-PSEUDO-TERM-LISTP))
    (2660 280
          (:REWRITE PSEUDO-TERM-LISTP-CDR-WHEN-PSEUDO-TERM-LISTP))
    (2124 420
          (:REWRITE CMR::PSEUDO-VAR-LIST-P-OF-CDR-WHEN-PSEUDO-VAR-LIST-P))
    (1750 210 (:DEFINITION LENGTH))
    (1748 1743 (:REWRITE DEFAULT-CDR))
    (1680 1680 (:TYPE-PRESCRIPTION LEN))
    (1400 280 (:DEFINITION LEN))
    (1260 1260
          (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
    (912 119
         (:REWRITE CMR::PSEUDO-TERM-SUBST-FIX-WHEN-PSEUDO-TERM-SUBST-P))
    (768 768
         (:REWRITE CMR::PSEUDO-VAR-LIST-P-WHEN-NOT-CONSP))
    (700 140 (:DEFINITION TRUE-LISTP))
    (659 159
         (:REWRITE CMR::PSEUDO-TERM-SUBST-P-OF-CDR-WHEN-PSEUDO-TERM-SUBST-P))
    (560 560 (:TYPE-PRESCRIPTION TRUE-LISTP))
    (560 280 (:REWRITE DEFAULT-+-2))
    (420 420 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
    (420 420
         (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
    (420 70 (:DEFINITION SYMBOL-LISTP))
    (416 413
         (:REWRITE CMR::PSEUDO-TERM-SUBST-P-WHEN-NOT-CONSP))
    (377 69
         (:REWRITE CMR::PSEUDO-VAR-P-OF-CAAR-WHEN-PSEUDO-TERM-SUBST-P))
    (360 64
         (:REWRITE CMR::PSEUDO-TERMP-OF-CDAR-WHEN-PSEUDO-TERM-SUBST-P))
    (350 350 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
    (280 280 (:REWRITE DEFAULT-+-1))
    (273 69
         (:REWRITE CMR::PSEUDO-VAR-P-OF-CAR-WHEN-PSEUDO-VAR-LIST-P))
    (140 140
         (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
    (70 70 (:REWRITE DEFAULT-COERCE-2))
    (70 70 (:REWRITE DEFAULT-COERCE-1))
    (33 6
        (:REWRITE CMR::PSEUDO-TERMP-OF-LOOKUP-IN-PSEUDO-TERM-SUBST)))
(CMR::BASE-EV-ALIST)
(CMR::LOOKUP-IN-BASE-EV-ALIST-SPLIT
 (461 47
      (:REWRITE BASE-EV-WHEN-PSEUDO-TERM-VAR))
 (461 47
      (:REWRITE BASE-EV-WHEN-PSEUDO-TERM-QUOTE))
 (461 47
      (:REWRITE BASE-EV-WHEN-PSEUDO-TERM-NULL))
 (461 47
      (:REWRITE BASE-EV-WHEN-PSEUDO-TERM-LAMBDA))
 (461 47
      (:REWRITE BASE-EV-WHEN-PSEUDO-TERM-FNCALL))
 (237 45
      (:REWRITE CMR::PSEUDO-VAR-P-OF-CAAR-WHEN-PSEUDO-TERM-SUBST-P))
 (230
     230
     (:REWRITE PSEUDO-TERM-KIND$INLINE-OF-PSEUDO-TERM-FIX-X-NORMALIZE-CONST))
 (206 201 (:REWRITE DEFAULT-CDR))
 (177 45
      (:REWRITE CMR::PSEUDO-VAR-P-OF-CAR-WHEN-PSEUDO-VAR-LIST-P))
 (60 15
     (:REWRITE CMR::PSEUDO-TERM-SUBST-P-OF-CDR-WHEN-PSEUDO-TERM-SUBST-P))
 (59 59
     (:REWRITE CMR::PSEUDO-TERM-SUBST-P-WHEN-NOT-CONSP))
 (47 47 (:REWRITE BASE-EV-OF-VARIABLE))
 (47 47 (:REWRITE BASE-EV-OF-QUOTE))
 (47 47 (:REWRITE BASE-EV-OF-LAMBDA))
 (44 44
     (:REWRITE CMR::PSEUDO-VAR-LIST-P-WHEN-NOT-CONSP)))