(EDP)
(=_E)
(C_=_E (1 1 (:TYPE-PRESCRIPTION C_=_E)))
(BINARY-+_E)
(BINARY-*_E)
(-_E)
(|0_E|)
(|1_E|)
(SIZE)
(Q_E)
(R_E)
(CLOSURE-LAWS)
(EQUIVALENCE-LAW)
(CONGRUENCE-LAWS)
(CLOSURE-OF-C_=_E)
(EQUIVALENCE-CLASS-LAWS (2 2 (:TYPE-PRESCRIPTION C_=_E)))
(COMMUTATIVITY-LAWS (3 3 (:REWRITE DEFAULT-+-2))
                    (3 3 (:REWRITE DEFAULT-+-1))
                    (3 3 (:REWRITE DEFAULT-*-2))
                    (3 3 (:REWRITE DEFAULT-*-1)))
(ASSOCIATIVITY-LAWS)
(LEFT-DISTRIBUTIVITY-LAW (6 2 (:LINEAR X*Y>1-POSITIVE))
                         (5 5 (:REWRITE DEFAULT-*-2))
                         (5 5 (:REWRITE DEFAULT-*-1))
                         (3 3 (:REWRITE DEFAULT-+-2))
                         (3 3 (:REWRITE DEFAULT-+-1))
                         (2 2 (:REWRITE DEFAULT-<-2))
                         (2 2 (:REWRITE DEFAULT-<-1)))
(LEFT-UNICITY-LAWS)
(RIGHT-INVERSE-LAW)
(ZERO-DIVISOR-LAW (1 1 (:REWRITE DEFAULT-*-2))
                  (1 1 (:REWRITE DEFAULT-*-1)))
(NATP-SIZE (2 1 (:TYPE-PRESCRIPTION NATP-SIZE)))
(CONGRUENCE-FOR-SIZE (4 2 (:TYPE-PRESCRIPTION NATP-SIZE)))
(CLOSURE-OF-Q_E-&-R_E)
(CONGRUENCE-FOR-Q_E-&-R_E)
(DIVISION-PROPERTY (6 2 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
                   (6 2 (:LINEAR X*Y>1-POSITIVE))
                   (2 2 (:REWRITE NUMERATOR-WHEN-INTEGERP))
                   (2 2 (:REWRITE DEFAULT-NUMERATOR))
                   (2 2 (:REWRITE DEFAULT-<-2))
                   (2 2 (:REWRITE DEFAULT-<-1))
                   (2 2 (:REWRITE DEFAULT-+-2))
                   (2 2 (:REWRITE DEFAULT-+-1))
                   (1 1 (:REWRITE FOLD-CONSTS-IN-*))
                   (1 1 (:REWRITE DEFAULT-UNARY-/))
                   (1 1 (:REWRITE DEFAULT-*-2))
                   (1 1 (:REWRITE DEFAULT-*-1)))
(SIZE-*_E)
(==_E)
(BINARY-++_E)
(BINARY-**_E)
(CLOSURE-LAWS-FOR-++_E-&-**_E)
(==_E-EQUIVALENCE-LAW (224 224 (:REWRITE CLOSURE-LAWS)))
(==_E-IMPLIES-IFF-EDP (87 37 (:REWRITE EQUIVALENCE-LAW))
                      (50 50 (:REWRITE CLOSURE-LAWS)))
(==_E-IMPLIES-==_E-++_E-1 (2590 16 (:REWRITE ZERO-DIVISOR-LAW)))
(==_E-IMPLIES-==_E-++_E-2 (2488 16 (:REWRITE ZERO-DIVISOR-LAW)))
(==_E-IMPLIES-==_E-**_E-1 (5180 32 (:REWRITE ZERO-DIVISOR-LAW)))
(==_E-IMPLIES-==_E-**_E-2 (4976 32 (:REWRITE ZERO-DIVISOR-LAW)))
(==_E-IMPLIES-==_E_-_E)
(C_==_E)
(==_E-C_==_E (596 596 (:REWRITE CLOSURE-LAWS)))
(==_E-IMPLIES-EQUAL-C_==_E (445 188 (:REWRITE EQUIVALENCE-LAW))
                           (256 256 (:REWRITE CLOSURE-LAWS))
                           (1 1 (:REWRITE CLOSURE-OF-C_=_E)))
(COMMUTATIVITY-LAWS-FOR-++_E-&-**_E)
(ASSOCIATIVITY-LAWS-FOR-++_E-&-**_E)
(LEFT-DISTRIBUTIVITY-LAW-FOR-++_E-&-**_E)
(LEFT-UNICITY-LAWS-FOR-++_E-&-**_E)
(RIGHT-INVERSE-LAW-FOR-++_E)
(ZERO-DIVISOR-LAW-FOR-**_E (208 82 (:REWRITE EQUIVALENCE-LAW)))
(NATP-SIZE-==_E (80 31 (:REWRITE EQUIVALENCE-LAW))
                (1 1 (:TYPE-PRESCRIPTION NATP-SIZE-==_E)))
(==_E-IMPLIES-EQUAL-SIZE (134 56 (:REWRITE EQUIVALENCE-LAW))
                         (78 78 (:REWRITE CLOSURE-LAWS))
                         (68 58 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
                         (58 58 (:TYPE-PRESCRIPTION NATP-SIZE)))
(QQ_E)
(RR_E)
(CLOSURE-OF-QQ_E-&-RR_E (236 91 (:REWRITE EQUIVALENCE-LAW)))
(==_E-IMPLIES-==_E-QQ_E-1)
(==_E-IMPLIES-==_E-QQ_E-2)
(==_E-IMPLIES-==_E-RR_E-1)
(==_E-IMPLIES-==_E-RR_E-2)
(DIVISION-PROPERTY-FOR-QQ_E-&-RR_E
     (70 5 (:REWRITE DEFAULT-<-1))
     (35 5
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (14 5 (:REWRITE DEFAULT-<-2)))
(SIZE-**_E (208 82 (:REWRITE EQUIVALENCE-LAW)))
(RIGHT-UNICITY-LAWS)
(RIGHT-DISTRIBUTIVITY-LAW)
(COMMUTATIVITY-2-LAWS)
(NULLITY-LAWS)
(INVOLUTION-LAW)
(INVERSE-DISTRIBUTIVE-LAW)
(INVERSE-CANCELLATION-LAWS)
(CANCELLATION-LAWS-FOR-++_E)
(FUNCTIONAL-COMMUTATIVITY-LAWS-1)
(|-_E-0|)
(EQUAL_-_E-ZERO)
(==_E-INVERSES-LAW)
(IDEMPOTENT-LAW)
(==_E_-_E-0_E)
(CANCELLATION-LAWS-FOR-**_E)
(PROJECTION-LAWS)
(COMMUTATIVITY-OF-==_E)
(PROJECTION-LAWS-1)
(|1_E-0_E|)
(DIVIDES-P)
(DIVIDES-P-SUFF)
(DIVIDES-P1)
(DIVIDES-P1-SUFF)
(DIVIDES-P-IMPLIES-DIVIDES-P1 (3740 14 (:REWRITE ZERO-DIVISOR-LAW))
                              (6 6 (:REWRITE DIVIDES-P-SUFF))
                              (1 1 (:REWRITE RIGHT-UNICITY-LAWS))
                              (1 1 (:REWRITE NULLITY-LAWS)))
(DIVIDES-P1-IMPLIES-DIVIDES-P (1609 604 (:REWRITE EQUIVALENCE-LAW))
                              (1339 6 (:REWRITE ZERO-DIVISOR-LAW))
                              (1 1 (:REWRITE DIVIDES-P1-SUFF)))
(DIVIDES-P-IFF-DIVIDES-P1)
(BOOLEANP-DIVIDES-P (4052 24 (:REWRITE ZERO-DIVISOR-LAW)))
(DIVIDES-P-=-DIVIDES-P1 (2 2 (:REWRITE DIVIDES-P1-SUFF))
                        (1 1 (:REWRITE DIVIDES-P-SUFF)))
(DIVIDES-PP-WITNESS)
(==_E-IMPLIES-==_E-DIVIDES-PP-WITNESS-1)
(==_E-IMPLIES-==_E-DIVIDES-PP-WITNESS-2)
(DIVIDES-PP)
(==_E-IMPLIES-EQUAL-DIVIDES-PP-1)
(==_E-IMPLIES-EQUAL-DIVIDES-PP-2)
(DIVIDES-PP-SUFF)
(DIVIDES-P1-=-DIVIDES-PP)
(DIVIDES-P-=-DIVIDES-PP)
(DIVIDES-PP-EDP-1 (1 1 (:REWRITE DIVIDES-PP-SUFF)))
(DIVIDES-PP-EDP-2 (2 2 (:REWRITE DIVIDES-PP-SUFF)))
(DIVIDES-PP-EDP-DIVIDES-PP-WITNESS (1 1 (:REWRITE DIVIDES-PP-SUFF)))
(GREATEST-DIVIDES-PP=0_E)
(LEAST-DIVIDES-PP=1_E)
(TRANSITIVITY-DIVIDES-PP-LEMMA (4 1 (:DEFINITION DIVIDES-PP)))
(TRANSITIVITY-DIVIDES-PP (14 14 (:REWRITE CLOSURE-LAWS))
                         (9 3 (:REWRITE PROJECTION-LAWS))
                         (6 6 (:REWRITE RIGHT-UNICITY-LAWS))
                         (6 6 (:REWRITE NULLITY-LAWS))
                         (2 2
                            (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E)))
(DIVIDES-PP-++_E (101 16 (:REWRITE TRANSITIVITY-DIVIDES-PP))
                 (26 26 (:REWRITE CLOSURE-LAWS))
                 (10 10 (:REWRITE RIGHT-UNICITY-LAWS))
                 (10 10 (:REWRITE NULLITY-LAWS))
                 (8 6 (:REWRITE PROJECTION-LAWS-1))
                 (5 5
                    (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
                 (4 4 (:REWRITE CANCELLATION-LAWS-FOR-++_E))
                 (2 2 (:REWRITE PROJECTION-LAWS)))
(DIVIDES-PP--_E (65 3 (:REWRITE DIVIDES-PP-++_E))
                (57 17 (:REWRITE TRANSITIVITY-DIVIDES-PP))
                (15 1 (:REWRITE DIVIDES-P1-SUFF))
                (10 10 (:REWRITE RIGHT-UNICITY-LAWS))
                (10 10 (:REWRITE NULLITY-LAWS))
                (6 4 (:REWRITE CANCELLATION-LAWS-FOR-++_E))
                (3 2 (:REWRITE PROJECTION-LAWS))
                (2 2 (:REWRITE PROJECTION-LAWS-1))
                (2 2 (:REWRITE EQUAL_-_E-ZERO))
                (2 2
                   (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E)))
(DIVIDES-PP-**_E (44 20 (:REWRITE TRANSITIVITY-DIVIDES-PP))
                 (20 20 (:REWRITE CLOSURE-LAWS))
                 (17 7 (:REWRITE PROJECTION-LAWS))
                 (8 8 (:REWRITE RIGHT-UNICITY-LAWS))
                 (8 8 (:REWRITE NULLITY-LAWS)))
(DIVIDES-PP-WITNESS-0_E (5 1
                           (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
                        (2 2 (:REWRITE TRANSITIVITY-DIVIDES-PP)))
(RR_E=0-IMPLIES-DIVIDES-PP (53 6
                               (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
                           (6 6 (:REWRITE TRANSITIVITY-DIVIDES-PP))
                           (4 4 (:REWRITE RIGHT-UNICITY-LAWS))
                           (4 4 (:REWRITE NULLITY-LAWS)))
(DIVIDES-PP-IMPLIES-RR_E=0-LEMMA (128 10 (:REWRITE DIVIDES-PP-SUFF))
                                 (29 1 (:REWRITE DIVIDES-PP-++_E))
                                 (22 10 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
                                 (19 10 (:REWRITE TRANSITIVITY-DIVIDES-PP))
                                 (15 5 (:REWRITE PROJECTION-LAWS))
                                 (7 7 (:REWRITE NULLITY-LAWS))
                                 (3 1 (:REWRITE PROJECTION-LAWS-1)))
(DIVIDES-PP-IMPLIES-RR_E=0-LEMMA-1
     (73 6
         (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
     (49 3 (:REWRITE DIVIDES-PP-SUFF))
     (12 3 (:DEFINITION DIVIDES-PP))
     (9 3 (:REWRITE PROJECTION-LAWS))
     (6 6 (:TYPE-PRESCRIPTION DIVIDES-PP))
     (6 6 (:REWRITE CLOSURE-LAWS))
     (3 3 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (3 3 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (3 3 (:REWRITE RIGHT-UNICITY-LAWS))
     (3 3 (:REWRITE NULLITY-LAWS)))
(DIVIDES-P-IMPLIES-RR_E=0 (64 10 (:REWRITE DIVIDES-PP-SUFF))
                          (41 41 (:TYPE-PRESCRIPTION NATP-SIZE))
                          (19 10 (:REWRITE TRANSITIVITY-DIVIDES-PP))
                          (14 1 (:REWRITE DEFAULT-<-1))
                          (10 10 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
                          (7 1
                             (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                          (6 2 (:REWRITE PROJECTION-LAWS))
                          (5 5 (:REWRITE RIGHT-UNICITY-LAWS))
                          (5 5 (:REWRITE NULLITY-LAWS))
                          (2 1 (:REWRITE DEFAULT-<-2)))
(DIVIDES-PP-IMPLIES-WITNESS=QQ_E (45 45 (:TYPE-PRESCRIPTION NATP-SIZE))
                                 (22 12 (:REWRITE DIVIDES-PP-SUFF))
                                 (19 12 (:REWRITE TRANSITIVITY-DIVIDES-PP))
                                 (12 12 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
                                 (8 8 (:REWRITE CANCELLATION-LAWS-FOR-**_E))
                                 (3 1 (:REWRITE PROJECTION-LAWS))
                                 (2 2 (:REWRITE CLOSURE-LAWS))
                                 (1 1 (:REWRITE NULLITY-LAWS)))
(ASSOCIATES-P)
(ASSOCIATES-PP)
(ASSOCIATES-P-=-ASSOCIATES-PP
     (1399 1 (:REWRITE DIVIDES-P-SUFF))
     (1396 487 (:REWRITE EQUIVALENCE-LAW))
     (1044 8 (:REWRITE ZERO-DIVISOR-LAW))
     (907 907 (:REWRITE CLOSURE-LAWS))
     (33 4 (:REWRITE DIVIDES-PP-SUFF))
     (22 22 (:EQUIVALENCE ==_E-EQUIVALENCE-LAW))
     (8 4 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (6 2 (:REWRITE PROJECTION-LAWS))
     (4 4 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (2 2 (:REWRITE RIGHT-UNICITY-LAWS))
     (2 2 (:REWRITE NULLITY-LAWS))
     (1 1
        (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E)))
(ASSOCIATES-PP-IS-AN-EQUIVALENCE
     (75 29 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (9 9 (:REWRITE NULLITY-LAWS))
     (6 6
        (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E)))
(==_E-IMPLIES-EQUAL-ASSOCIATES-PP-1
     (87 37 (:REWRITE EQUIVALENCE-LAW))
     (62 4 (:REWRITE DIVIDES-PP-SUFF))
     (58 58 (:REWRITE CLOSURE-LAWS))
     (12 4 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (12 4 (:REWRITE PROJECTION-LAWS))
     (4 4 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (4 4 (:REWRITE RIGHT-UNICITY-LAWS))
     (4 4 (:REWRITE NULLITY-LAWS))
     (2 2
        (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E)))
(==_E-IMPLIES-EQUAL-ASSOCIATES-PP-2
     (87 37 (:REWRITE EQUIVALENCE-LAW))
     (62 4 (:REWRITE DIVIDES-PP-SUFF))
     (58 58 (:REWRITE CLOSURE-LAWS))
     (12 4 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (12 4 (:REWRITE PROJECTION-LAWS))
     (4 4 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (4 4 (:REWRITE RIGHT-UNICITY-LAWS))
     (4 4 (:REWRITE NULLITY-LAWS))
     (2 2
        (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E)))
(==_E-REFINES-ASSOCIATES-PP)
(ASSOCIATES-PP-IMPLIES-EQUAL-DIVIDES-PP-1
     (514 284
          (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (292 292 (:REWRITE CLOSURE-LAWS))
     (284 284 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (106 106 (:REWRITE RIGHT-UNICITY-LAWS))
     (106 106 (:REWRITE NULLITY-LAWS))
     (96 32 (:REWRITE PROJECTION-LAWS)))
(ASSOCIATES-PP-IMPLIES-EQUAL-DIVIDES-PP-2
     (751 393
          (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (393 393 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (388 388 (:REWRITE CLOSURE-LAWS))
     (152 152 (:REWRITE RIGHT-UNICITY-LAWS))
     (152 152 (:REWRITE NULLITY-LAWS))
     (22 22
         (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E)))
(DIVIDES-PP-<=-SIZE (215 215 (:TYPE-PRESCRIPTION NATP-SIZE))
                    (60 3 (:REWRITE DEFAULT-<-2))
                    (51 6
                        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                    (42 3 (:REWRITE DEFAULT-<-1))
                    (29 5 (:REWRITE DIVIDES-PP-SUFF))
                    (9 5 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
                    (5 5 (:REWRITE TRANSITIVITY-DIVIDES-PP))
                    (3 1 (:REWRITE SIZE-**_E))
                    (3 1 (:LINEAR SIZE-**_E))
                    (1 1 (:REWRITE RIGHT-UNICITY-LAWS)))
(ASSOCIATES-PP-IMPLIES-EQUAL-SIZE-LEMMA-1
     (451 451 (:TYPE-PRESCRIPTION NATP-SIZE))
     (241 32 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (129 6 (:REWRITE DIVIDES-P-IMPLIES-RR_E=0))
     (72 6
         (:REWRITE DIVIDES-PP-IMPLIES-RR_E=0-LEMMA-1))
     (54 6
         (:REWRITE DIVIDES-PP-IMPLIES-WITNESS=QQ_E))
     (32 32 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (28 4
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (28 2 (:REWRITE DEFAULT-<-2))
     (28 2 (:REWRITE DEFAULT-<-1))
     (12 2 (:REWRITE DIVIDES-PP-<=-SIZE))
     (11 1
         (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
     (3 3
        (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E)))
(ASSOCIATES-PP-IMPLIES-EQUAL-SIZE-LEMMA-2
     (483 483 (:TYPE-PRESCRIPTION NATP-SIZE))
     (80 8
         (:REWRITE DIVIDES-PP-IMPLIES-RR_E=0-LEMMA-1))
     (56 8
         (:REWRITE DIVIDES-PP-IMPLIES-WITNESS=QQ_E))
     (42 6
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (42 3 (:REWRITE DEFAULT-<-2))
     (42 3 (:REWRITE DEFAULT-<-1))
     (36 36 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (30 3 (:REWRITE DIVIDES-PP-<=-SIZE))
     (11 1
         (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
     (3 3
        (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E)))
(ASSOCIATES-PP-IMPLIES-EQUAL-SIZE (24 24 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
                                  (24 24 (:TYPE-PRESCRIPTION NATP-SIZE)))
(UNIT-P)
(UNIT-P1)
(UNIT-PP)
(UNIT-P-=-UNIT-P1)
(UNIT-P1-=-UNIT-PP)
(UNIT-P-=-UNIT-PP)
(==_E-IMPLIES-EQUAL-UNIT-PP)
(ASSOCIATES-PP-IMPLIES-EQUAL-UNIT-PP)
(UNIT-PP-1_E (5 1 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
             (2 2 (:EQUIVALENCE ==_E-EQUIVALENCE-LAW))
             (1 1 (:REWRITE TRANSITIVITY-DIVIDES-PP))
             (1 1 (:REWRITE |1_E-0_E|)))
(UNIT-PP-_-_E-1_E (10 2 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
                  (2 2 (:REWRITE TRANSITIVITY-DIVIDES-PP))
                  (2 1 (:REWRITE NULLITY-LAWS))
                  (1 1
                     (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
                  (1 1 (:REWRITE |-_E-0|)))
(SIZE-UNIT-PP=SIZE-1_E (58 46 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
                       (46 46 (:TYPE-PRESCRIPTION NATP-SIZE))
                       (24 7 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
                       (19 1
                           (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
                       (3 3 (:REWRITE |1_E-0_E|))
                       (1 1 (:REWRITE RIGHT-UNICITY-LAWS))
                       (1 1 (:REWRITE NULLITY-LAWS)))
(SIZE-UNIT-P=SIZE-1_E (52 52 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
                      (52 52 (:TYPE-PRESCRIPTION NATP-SIZE)))
(SIZE->=-SIZE-1_E (44 44 (:TYPE-PRESCRIPTION NATP-SIZE))
                  (13 1 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
                  (5 1
                     (:REWRITE DIVIDES-PP-IMPLIES-RR_E=0-LEMMA-1))
                  (2 1
                     (:REWRITE DIVIDES-PP-IMPLIES-WITNESS=QQ_E))
                  (2 1 (:REWRITE DIVIDES-P-IMPLIES-RR_E=0))
                  (1 1 (:REWRITE TRANSITIVITY-DIVIDES-PP))
                  (1 1 (:REWRITE CLOSURE-LAWS))
                  (1 1 (:REWRITE |1_E-0_E|)))
(RR_E-1_E-X=0_E (20 1 (:REWRITE DIVIDES-P-IMPLIES-RR_E=0))
                (17 17 (:TYPE-PRESCRIPTION NATP-SIZE))
                (15 1
                    (:REWRITE DIVIDES-PP-IMPLIES-RR_E=0-LEMMA-1))
                (14 2 (:REWRITE DIVIDES-PP-SUFF))
                (12 1
                    (:REWRITE DIVIDES-PP-IMPLIES-WITNESS=QQ_E))
                (8 2 (:DEFINITION DIVIDES-PP))
                (4 4 (:TYPE-PRESCRIPTION DIVIDES-PP))
                (4 2 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
                (4 2
                   (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
                (3 1 (:REWRITE |1_E-0_E|))
                (2 2 (:REWRITE TRANSITIVITY-DIVIDES-PP))
                (1 1 (:REWRITE RIGHT-UNICITY-LAWS))
                (1 1 (:REWRITE NULLITY-LAWS)))
(SIZE=SIZE-1_E-IMPLIES-UNIT-PP (29 29 (:TYPE-PRESCRIPTION NATP-SIZE))
                               (6 3 (:LINEAR SIZE->=-SIZE-1_E))
                               (1 1 (:REWRITE |1_E-0_E|)))
(SIZE=SIZE-1_E-IMPLIES-UNIT-P (188 62 (:REWRITE EQUIVALENCE-LAW))
                              (147 3 (:LINEAR SIZE->=-SIZE-1_E))
                              (1 1 (:REWRITE |1_E-0_E|)))
(SIZE-<-SIZE-**_E-LEMMA-1 (203 10 (:REWRITE DIVIDES-P-IMPLIES-RR_E=0))
                          (123 6 (:REWRITE DIVIDES-PP-SUFF))
                          (78 6 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
                          (64 17 (:REWRITE PROJECTION-LAWS))
                          (51 6 (:DEFINITION DIVIDES-PP))
                          (50 10
                              (:REWRITE DIVIDES-PP-IMPLIES-RR_E=0-LEMMA-1))
                          (49 1 (:REWRITE DIVIDES-PP-<=-SIZE))
                          (30 5
                              (:REWRITE DIVIDES-PP-IMPLIES-WITNESS=QQ_E))
                          (20 20 (:TYPE-PRESCRIPTION DIVIDES-PP))
                          (18 18 (:TYPE-PRESCRIPTION NATP-SIZE))
                          (12 6
                              (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
                          (6 6 (:REWRITE TRANSITIVITY-DIVIDES-PP))
                          (6 3 (:REWRITE NULLITY-LAWS)))
(SIZE-<-SIZE-**_E-LEMMA-2 (585 24 (:REWRITE DIVIDES-P-IMPLIES-RR_E=0))
                          (293 31 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
                          (288 24
                               (:REWRITE DIVIDES-PP-IMPLIES-RR_E=0-LEMMA-1))
                          (258 258 (:TYPE-PRESCRIPTION NATP-SIZE))
                          (222 21
                               (:REWRITE DIVIDES-PP-IMPLIES-WITNESS=QQ_E))
                          (213 27 (:DEFINITION DIVIDES-PP))
                          (57 45
                              (:REWRITE ASSOCIATIVITY-LAWS-FOR-++_E-&-**_E))
                          (54 27
                              (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
                          (42 3 (:REWRITE DEFAULT-<-1))
                          (30 18 (:REWRITE NULLITY-LAWS))
                          (29 29 (:REWRITE TRANSITIVITY-DIVIDES-PP))
                          (21 3
                              (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                          (12 12
                              (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
                          (9 1 (:REWRITE CANCELLATION-LAWS-FOR-**_E))
                          (6 3 (:REWRITE DEFAULT-<-2)))
(SIZE-<-SIZE-**_E-LEMMA-3 (362 362 (:TYPE-PRESCRIPTION NATP-SIZE))
                          (96 4 (:REWRITE DIVIDES-PP-<=-SIZE))
                          (92 17
                              (:REWRITE DIVIDES-PP-IMPLIES-RR_E=0-LEMMA-1))
                          (65 5 (:REWRITE RR_E-1_E-X=0_E))
                          (56 4 (:REWRITE DEFAULT-<-1))
                          (51 11
                              (:REWRITE DIVIDES-PP-IMPLIES-WITNESS=QQ_E))
                          (29 12
                              (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
                          (28 4
                              (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                          (19 19 (:REWRITE TRANSITIVITY-DIVIDES-PP))
                          (12 2
                              (:LINEAR DIVISION-PROPERTY-FOR-QQ_E-&-RR_E))
                          (9 7 (:REWRITE NULLITY-LAWS))
                          (9 3 (:LINEAR SIZE-**_E))
                          (8 4 (:REWRITE DEFAULT-<-2))
                          (2 2 (:REWRITE GREATEST-DIVIDES-PP=0_E)))
(SIZE-<-SIZE-**_E (380 380 (:TYPE-PRESCRIPTION NATP-SIZE))
                  (108 2 (:REWRITE DIVIDES-PP-<=-SIZE))
                  (39 3 (:REWRITE RR_E-1_E-X=0_E))
                  (30 8 (:REWRITE PROJECTION-LAWS))
                  (30 4
                      (:REWRITE DIVIDES-PP-IMPLIES-RR_E=0-LEMMA-1))
                  (28 2 (:REWRITE DEFAULT-<-2))
                  (18 6
                      (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
                  (18 4
                      (:REWRITE DIVIDES-PP-IMPLIES-WITNESS=QQ_E))
                  (14 2
                      (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                  (8 8 (:REWRITE TRANSITIVITY-DIVIDES-PP))
                  (8 6
                     (:REWRITE ASSOCIATIVITY-LAWS-FOR-++_E-&-**_E))
                  (6 4 (:REWRITE RIGHT-UNICITY-LAWS))
                  (6 4 (:REWRITE NULLITY-LAWS))
                  (4 2 (:REWRITE DEFAULT-<-1))
                  (2 2 (:REWRITE |1_E-0_E|)))
(UNIT-PP-DIVIDES-PP-WITNESS (19 1
                                (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
                            (10 4 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
                            (9 1
                               (:REWRITE DIVIDES-PP-IMPLIES-WITNESS=QQ_E))
                            (4 4 (:REWRITE TRANSITIVITY-DIVIDES-PP))
                            (2 2 (:REWRITE CLOSURE-LAWS))
                            (1 1 (:REWRITE RIGHT-UNICITY-LAWS))
                            (1 1 (:REWRITE NULLITY-LAWS)))
(DIVIDES-PP-WITNESS-DIVIDES-PP-WITNESS
     (66 16 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (6 3 (:REWRITE DIVIDES-PP-WITNESS-0_E))
     (3 3 (:REWRITE |1_E-0_E|)))
(UNIT-PP-CLOSURE-**_E (53 22 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
                      (52 8
                          (:REWRITE DIVIDES-PP-IMPLIES-WITNESS=QQ_E))
                      (22 22 (:REWRITE TRANSITIVITY-DIVIDES-PP))
                      (16 16 (:REWRITE CLOSURE-LAWS))
                      (8 7 (:REWRITE NULLITY-LAWS))
                      (6 2 (:REWRITE ZERO-DIVISOR-LAW-FOR-**_E)))
(INVERSE-CANCELLATION-LAWS-**_E)
(UNIT-PP-**_E-INVERSE (21 1
                          (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
                      (17 3 (:REWRITE DIVIDES-PP-SUFF))
                      (11 1
                          (:REWRITE DIVIDES-PP-IMPLIES-WITNESS=QQ_E))
                      (7 3 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
                      (3 3 (:REWRITE TRANSITIVITY-DIVIDES-PP))
                      (2 2 (:REWRITE CLOSURE-LAWS))
                      (1 1 (:REWRITE RIGHT-UNICITY-LAWS))
                      (1 1 (:REWRITE NULLITY-LAWS)))
(UNIT-PP-INVERSE-DISTRIBUTIVE-LAW
     (333 25 (:REWRITE UNIT-PP-**_E-INVERSE))
     (249 8
          (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
     (76 32 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (40 14
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (32 32 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (32 32 (:REWRITE CLOSURE-LAWS))
     (27 12
         (:REWRITE INVERSE-CANCELLATION-LAWS-**_E))
     (23 23 (:REWRITE RIGHT-UNICITY-LAWS))
     (16 16 (:REWRITE NULLITY-LAWS))
     (9 1
        (:REWRITE DIVIDES-PP-IMPLIES-WITNESS=QQ_E)))
(DIVIDES-PP-WITNESS-1_E (8 1 (:REWRITE UNIT-PP-**_E-INVERSE))
                        (6 2 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
                        (6 1
                           (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
                        (5 1
                           (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
                        (2 2 (:REWRITE TRANSITIVITY-DIVIDES-PP))
                        (2 2 (:REWRITE |1_E-0_E|))
                        (1 1 (:TYPE-PRESCRIPTION UNIT-PP))
                        (1 1 (:REWRITE UNIT-PP-1_E)))
(DIVIDES-PP-WITNESS-_-_E-1_E
     (393 9
          (:REWRITE DIVIDES-PP-IMPLIES-WITNESS=QQ_E))
     (273 13 (:DEFINITION DIVIDES-PP))
     (200 32 (:REWRITE UNIT-PP-**_E-INVERSE))
     (185 13 (:REWRITE DIVIDES-PP-SUFF))
     (166 18
          (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
     (164 19
          (:REWRITE LEFT-UNICITY-LAWS-FOR-++_E-&-**_E))
     (111 35
          (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (45 13 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (26 26 (:TYPE-PRESCRIPTION DIVIDES-PP))
     (16 8 (:REWRITE NULLITY-LAWS))
     (13 13 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (8 8 (:REWRITE |-_E-0|))
     (1 1 (:REWRITE |1_E-0_E|)))
(NOT-UNIT-PP-0_E (28 3 (:REWRITE DIVIDES-PP-SUFF))
                 (19 2 (:REWRITE UNIT-PP-**_E-INVERSE))
                 (11 1
                     (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
                 (6 3 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
                 (3 3 (:REWRITE TRANSITIVITY-DIVIDES-PP))
                 (2 1
                    (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP)))
(UNIT-PP-0_E (2 1 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
             (1 1 (:REWRITE TRANSITIVITY-DIVIDES-PP))
             (1 1 (:REWRITE |1_E-0_E|)))
(UNIT-PP-EDP)
(UNIT-PP-**_E=>UNIT-PP-FACTOR-LEFT
     (735 48 (:REWRITE UNIT-PP-**_E-INVERSE))
     (405 114
          (:REWRITE INVERSE-CANCELLATION-LAWS-**_E))
     (175 9 (:REWRITE UNIT-PP-CLOSURE-**_E))
     (114 26
          (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
     (106 43 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (79 43 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (64 29
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (49 2
         (:REWRITE UNIT-PP-INVERSE-DISTRIBUTIVE-LAW))
     (33 11 (:REWRITE ZERO-DIVISOR-LAW-FOR-**_E))
     (32 32 (:REWRITE CLOSURE-LAWS))
     (17 12 (:REWRITE RIGHT-UNICITY-LAWS))
     (15 10 (:REWRITE NULLITY-LAWS))
     (6 6 (:REWRITE LEAST-DIVIDES-PP=1_E))
     (6 6 (:REWRITE |1_E-0_E|))
     (6 2
        (:REWRITE DIVIDES-PP-IMPLIES-WITNESS=QQ_E)))
(UNIT-PP-**_E=>UNIT-PP-FACTOR-RIGHT
     (419 24 (:REWRITE UNIT-PP-**_E-INVERSE))
     (178 78
          (:REWRITE INVERSE-CANCELLATION-LAWS-**_E))
     (103 2 (:REWRITE UNIT-PP-CLOSURE-**_E))
     (55 19 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (33 11
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (33 4
         (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
     (20 20 (:REWRITE CLOSURE-LAWS))
     (18 6 (:REWRITE ZERO-DIVISOR-LAW-FOR-**_E))
     (14 11 (:REWRITE RIGHT-UNICITY-LAWS))
     (14 2 (:REWRITE COMMUTATIVITY-2-LAWS))
     (10 7 (:REWRITE NULLITY-LAWS))
     (1 1 (:REWRITE |1_E-0_E|)))
(REDUCIBLE-P)
(REDUCIBLE-P-SUFF (4 4 (:DEFINITION MV-NTH)))
(REDUCIBLE-P1)
(REDUCIBLE-P1-SUFF (4 4 (:DEFINITION MV-NTH)))
(REDUCIBLE-P1-SUFF-1 (220 4
                          (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
                     (216 74 (:REWRITE EQUIVALENCE-LAW))
                     (142 142 (:REWRITE CLOSURE-LAWS)))
(REDUCIBLE-P1-SUFF-2 (13808 1 (:REWRITE REDUCIBLE-P1-SUFF))
                     (13781 16 (:DEFINITION UNIT-P1))
                     (9472 12 (:DEFINITION DIVIDES-P1))
                     (7956 44 (:REWRITE ZERO-DIVISOR-LAW))
                     (4293 16 (:REWRITE DIVIDES-P1-SUFF))
                     (162 2
                          (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
                     (24 24 (:EQUIVALENCE ==_E-EQUIVALENCE-LAW))
                     (16 16 (:TYPE-PRESCRIPTION UNIT-P1))
                     (12 10 (:REWRITE NULLITY-LAWS))
                     (10 6 (:REWRITE RIGHT-UNICITY-LAWS))
                     (8 8
                        (:REWRITE LEFT-UNICITY-LAWS-FOR-++_E-&-**_E))
                     (2 1
                        (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E)))
(REDUCIBLE-P-IMPLIES-REDUCIBLE-P1
     (393 135 (:REWRITE EQUIVALENCE-LAW))
     (390 10
          (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (310 310 (:REWRITE CLOSURE-LAWS))
     (106 2 (:REWRITE REDUCIBLE-P1-SUFF))
     (84 8 (:DEFINITION UNIT-P1))
     (60 8 (:REWRITE DIVIDES-P1-SUFF))
     (48 1 (:REWRITE REDUCIBLE-P-SUFF))
     (20 20 (:EQUIVALENCE ==_E-EQUIVALENCE-LAW))
     (16 4 (:DEFINITION DIVIDES-P1))
     (12 8 (:REWRITE NULLITY-LAWS))
     (8 8 (:TYPE-PRESCRIPTION UNIT-P1))
     (8 4 (:REWRITE RIGHT-UNICITY-LAWS))
     (4 4 (:REWRITE DEFAULT-CDR))
     (4 4 (:REWRITE DEFAULT-CAR)))
(REDUCIBLE-P-SUFF-1 (234 76 (:REWRITE EQUIVALENCE-LAW))
                    (225 4
                         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P)))
(REDUCIBLE-P-SUFF-2 (20011 6531 (:REWRITE EQUIVALENCE-LAW))
                    (19473 1 (:REWRITE REDUCIBLE-P-SUFF))
                    (19357 16 (:DEFINITION UNIT-P))
                    (14206 91 (:REWRITE ZERO-DIVISOR-LAW))
                    (13280 12 (:DEFINITION DIVIDES-P))
                    (6061 16 (:REWRITE DIVIDES-P-SUFF))
                    (89 16
                        (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
                    (16 16 (:TYPE-PRESCRIPTION UNIT-P))
                    (10 6 (:REWRITE LEFT-UNICITY-LAWS)))
(REDUCIBLE-P1-IMPLIES-REDUCIBLE-P
     (1412 2 (:REWRITE REDUCIBLE-P-SUFF))
     (1326 338 (:REWRITE EQUIVALENCE-LAW))
     (1324 8 (:DEFINITION UNIT-P))
     (1026 1026 (:REWRITE CLOSURE-LAWS))
     (936 4 (:DEFINITION DIVIDES-P))
     (584 12 (:REWRITE ZERO-DIVISOR-LAW))
     (380 8 (:REWRITE DIVIDES-P-SUFF))
     (66 8
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (15 1 (:REWRITE REDUCIBLE-P1-SUFF))
     (8 8 (:TYPE-PRESCRIPTION UNIT-P))
     (8 4 (:REWRITE LEFT-UNICITY-LAWS))
     (4 4 (:REWRITE DEFAULT-CDR))
     (4 4 (:REWRITE DEFAULT-CAR))
     (1 1 (:REWRITE REDUCIBLE-P1-SUFF-2)))
(REDUCIBLE-P-IFF-REDUCIBLE-P1)
(BOOLEANP-REDUCIBLE-P (6032 36 (:REWRITE ZERO-DIVISOR-LAW))
                      (2382 22
                            (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
                      (29 29 (:REWRITE DEFAULT-CDR))
                      (29 29 (:REWRITE DEFAULT-CAR)))
(REDUCIBLE-P-=-REDUCIBLE-P1 (706 1 (:REWRITE REDUCIBLE-P-SUFF))
                            (663 169 (:REWRITE EQUIVALENCE-LAW))
                            (662 4 (:DEFINITION UNIT-P))
                            (554 554 (:REWRITE CLOSURE-LAWS))
                            (468 2 (:DEFINITION DIVIDES-P))
                            (292 6 (:REWRITE ZERO-DIVISOR-LAW))
                            (190 4 (:REWRITE DIVIDES-P-SUFF))
                            (106 2 (:REWRITE REDUCIBLE-P1-SUFF))
                            (84 8 (:DEFINITION UNIT-P1))
                            (60 8 (:REWRITE DIVIDES-P1-SUFF))
                            (33 4
                                (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
                            (20 20 (:EQUIVALENCE ==_E-EQUIVALENCE-LAW))
                            (16 4 (:DEFINITION DIVIDES-P1))
                            (12 8 (:REWRITE NULLITY-LAWS))
                            (8 8 (:TYPE-PRESCRIPTION UNIT-P1))
                            (8 4 (:REWRITE RIGHT-UNICITY-LAWS))
                            (4 4 (:TYPE-PRESCRIPTION UNIT-P))
                            (4 2 (:REWRITE LEFT-UNICITY-LAWS))
                            (2 2 (:REWRITE REDUCIBLE-P1-SUFF-2))
                            (1 1 (:REWRITE REDUCIBLE-P-SUFF-2)))
(REDUCIBLE-PP-WITNESS)
(==_E-IMPLIES-EQUAL-REDUCIBLE-PP-WITNESS)
(REDUCIBLE-PP)
(==_E-IMPLIES-EQUAL-REDUCIBLE-PP
     (346 32 (:REWRITE DIVIDES-PP-SUFF))
     (284 20 (:REWRITE UNIT-PP-**_E-INVERSE))
     (90 10
         (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
     (76 32 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (64 64 (:REWRITE CLOSURE-LAWS))
     (42 14
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (32 32 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (22 22 (:REWRITE RIGHT-UNICITY-LAWS))
     (22 22 (:REWRITE NULLITY-LAWS))
     (4 4 (:REWRITE DEFAULT-CDR))
     (4 4 (:REWRITE DEFAULT-CAR)))
(REDUCIBLE-P1-SUFF-3 (1702 135 (:REWRITE DIVIDES-PP-SUFF))
                     (1451 92 (:REWRITE UNIT-PP-**_E-INVERSE))
                     (1264 53 (:REWRITE DIVIDES-P1-SUFF))
                     (536 66
                          (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
                     (376 376 (:REWRITE CLOSURE-LAWS))
                     (277 135
                          (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
                     (135 135 (:REWRITE TRANSITIVITY-DIVIDES-PP))
                     (132 132 (:REWRITE RIGHT-UNICITY-LAWS))
                     (132 132 (:REWRITE NULLITY-LAWS))
                     (126 42
                          (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
                     (16 16 (:REWRITE REDUCIBLE-P1-SUFF-2)))
(REDUCIBLE-PP-SUFF (860 56 (:REWRITE UNIT-PP-**_E-INVERSE))
                   (238 238 (:REWRITE CLOSURE-LAWS))
                   (209 25
                        (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
                   (202 1 (:REWRITE REDUCIBLE-P1-SUFF))
                   (197 81 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
                   (138 46
                        (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
                   (81 81 (:REWRITE TRANSITIVITY-DIVIDES-PP))
                   (80 78 (:REWRITE NULLITY-LAWS))
                   (78 74 (:REWRITE RIGHT-UNICITY-LAWS))
                   (21 21 (:REWRITE DEFAULT-CDR))
                   (21 21 (:REWRITE DEFAULT-CAR))
                   (8 8
                      (:REWRITE LEFT-UNICITY-LAWS-FOR-++_E-&-**_E))
                   (1 1 (:REWRITE REDUCIBLE-P1-SUFF-2)))
(REDUCIBLE-P1-IMPLIES-REDUCIBLE-PP
     (155 5 (:REWRITE REDUCIBLE-P1-SUFF-3))
     (75 75 (:REWRITE CLOSURE-LAWS))
     (75 5 (:REWRITE REDUCIBLE-P1-SUFF))
     (74 36
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (20 10 (:REWRITE UNIT-PP-0_E))
     (18 18 (:REWRITE DEFAULT-CDR))
     (10 10 (:REWRITE UNIT-PP-1_E))
     (10 10 (:REWRITE NOT-UNIT-PP-0_E))
     (7 7 (:REWRITE REDUCIBLE-PP-SUFF))
     (5 5 (:REWRITE REDUCIBLE-P1-SUFF-2))
     (5 5 (:REWRITE |1_E-0_E|)))
(REDUCIBLE-PP-IMPLIES-REDUCIBLE-P1
     (217 7 (:REWRITE REDUCIBLE-P1-SUFF-3))
     (109 41
          (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (105 105 (:REWRITE CLOSURE-LAWS))
     (105 7 (:REWRITE REDUCIBLE-P1-SUFF))
     (56 56 (:TYPE-PRESCRIPTION UNIT-P1))
     (28 14 (:REWRITE UNIT-PP-0_E))
     (14 14 (:REWRITE UNIT-PP-1_E))
     (14 14 (:REWRITE NOT-UNIT-PP-0_E))
     (8 8 (:REWRITE DEFAULT-CDR))
     (7 7 (:REWRITE REDUCIBLE-P1-SUFF-2))
     (7 7 (:REWRITE |1_E-0_E|))
     (5 5 (:REWRITE REDUCIBLE-PP-SUFF)))
(REDUCIBLE-P1-=-REDUCIBLE-PP
     (87 1 (:REWRITE REDUCIBLE-P1-SUFF-3))
     (58 2 (:DEFINITION UNIT-PP))
     (53 1 (:REWRITE REDUCIBLE-P1-SUFF))
     (51 51 (:REWRITE CLOSURE-LAWS))
     (42 4 (:DEFINITION UNIT-P1))
     (34 2 (:DEFINITION DIVIDES-PP))
     (30 4 (:REWRITE DIVIDES-P1-SUFF))
     (24 4 (:REWRITE DIVIDES-PP-SUFF))
     (22 2
         (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
     (20 20 (:EQUIVALENCE ==_E-EQUIVALENCE-LAW))
     (12 8 (:REWRITE NULLITY-LAWS))
     (10 4
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (8 4 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (8 2 (:DEFINITION DIVIDES-P1))
     (6 6 (:TYPE-PRESCRIPTION UNIT-PP))
     (6 6 (:TYPE-PRESCRIPTION DIVIDES-PP))
     (4 4 (:TYPE-PRESCRIPTION UNIT-P1))
     (4 4 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (4 2 (:REWRITE UNIT-PP-0_E))
     (4 2 (:REWRITE UNIT-PP-**_E-INVERSE))
     (4 2 (:REWRITE RIGHT-UNICITY-LAWS))
     (2 2 (:REWRITE UNIT-PP-1_E))
     (2 2 (:REWRITE NOT-UNIT-PP-0_E))
     (1 1 (:REWRITE REDUCIBLE-PP-SUFF))
     (1 1 (:REWRITE REDUCIBLE-P1-SUFF-2))
     (1 1 (:REWRITE |1_E-0_E|)))
(REDUCIBLE-P-=-REDUCIBLE-PP)
(REDUCIBLE-PP-EDP (276 12 (:REWRITE DIVIDES-PP-SUFF))
                  (188 8 (:REWRITE UNIT-PP-**_E-INVERSE))
                  (106 60
                       (:REWRITE INVERSE-CANCELLATION-LAWS-**_E))
                  (36 4
                      (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
                  (28 12 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
                  (24 24 (:REWRITE CLOSURE-LAWS))
                  (24 8
                      (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
                  (20 20 (:TYPE-PRESCRIPTION DIVIDES-PP))
                  (14 14 (:REWRITE DEFAULT-CDR))
                  (14 14 (:REWRITE DEFAULT-CAR))
                  (14 2 (:REWRITE COMMUTATIVITY-2-LAWS))
                  (12 12 (:REWRITE TRANSITIVITY-DIVIDES-PP))
                  (12 12
                      (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
                  (10 8
                      (:REWRITE LEFT-DISTRIBUTIVITY-LAW-FOR-++_E-&-**_E))
                  (8 8 (:TYPE-PRESCRIPTION UNIT-PP))
                  (8 8 (:REWRITE RIGHT-UNICITY-LAWS))
                  (8 8 (:REWRITE NULLITY-LAWS))
                  (5 5 (:REWRITE REDUCIBLE-PP-SUFF)))
(REDUCIBLE-PP-0_E (3 1 (:REWRITE UNIT-PP-0_E))
                  (1 1 (:REWRITE REDUCIBLE-PP-SUFF)))
(UNIT-PP-NOT-REDUCIBLE-PP (59 18
                              (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
                          (8 8 (:REWRITE DEFAULT-CAR))
                          (8 2 (:REWRITE ZERO-DIVISOR-LAW-FOR-**_E))
                          (7 7 (:REWRITE REDUCIBLE-PP-SUFF))
                          (7 7 (:REWRITE DEFAULT-CDR))
                          (7 2 (:REWRITE UNIT-PP-CLOSURE-**_E))
                          (1 1
                             (:REWRITE CLOSURE-LAWS-FOR-++_E-&-**_E)))
(IRREDUCIBLE-P)
(IRREDUCIBLE-PP)
(==_E-IMPLIES-EQUAL-IRREDUCIBLE-PP
     (198 18 (:REWRITE DIVIDES-PP-SUFF))
     (122 10 (:REWRITE UNIT-PP-**_E-INVERSE))
     (68 2 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
     (54 6
         (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
     (42 18 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (36 36 (:REWRITE CLOSURE-LAWS))
     (36 12
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (18 18 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (12 12 (:REWRITE RIGHT-UNICITY-LAWS))
     (12 12 (:REWRITE NULLITY-LAWS))
     (2 2 (:REWRITE REDUCIBLE-PP-SUFF))
     (2 2 (:REWRITE DEFAULT-CDR))
     (2 2 (:REWRITE DEFAULT-CAR)))
(IRREDUCIBLE-P-=-IRREDUCIBLE-PP (281 101 (:REWRITE EQUIVALENCE-LAW))
                                (279 1 (:REWRITE REDUCIBLE-P-SUFF))
                                (189 189 (:REWRITE CLOSURE-LAWS))
                                (133 1 (:REWRITE ZERO-DIVISOR-LAW))
                                (110 10
                                     (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
                                (10 2 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
                                (8 4
                                   (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
                                (4 4 (:EQUIVALENCE ==_E-EQUIVALENCE-LAW))
                                (2 2 (:REWRITE REDUCIBLE-PP-SUFF))
                                (1 1 (:REWRITE REDUCIBLE-P-SUFF-2)))
(IRREDUCIBLE-PP-NOT-0_E (6 1 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
                        (5 3 (:REWRITE UNIT-PP-0_E))
                        (3 2
                           (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
                        (1 1 (:REWRITE |1_E-0_E|)))
(IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR)
(IRREDUCIBLE-FACTORS-1
     (11358 24 (:LINEAR SIZE-<-SIZE-**_E))
     (10522 538
            (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
     (10366 26 (:DEFINITION IRREDUCIBLE-PP))
     (7068 616
           (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (4602 354 (:REWRITE UNIT-PP-**_E-INVERSE))
     (3412 106 (:REWRITE DIVIDES-P-IMPLIES-RR_E=0))
     (2604 36 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
     (2458 106
           (:REWRITE DIVIDES-PP-IMPLIES-RR_E=0-LEMMA-1))
     (2140 106
           (:REWRITE DIVIDES-PP-IMPLIES-WITNESS=QQ_E))
     (1733 303
           (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
     (1232 1232 (:TYPE-PRESCRIPTION NATP-SIZE))
     (707 257
          (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (616 616 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (514 36 (:REWRITE REDUCIBLE-PP-SUFF))
     (354 18 (:REWRITE DIVIDES-PP-<=-SIZE))
     (308 98 (:REWRITE RR_E-1_E-X=0_E))
     (230 230 (:REWRITE RIGHT-UNICITY-LAWS))
     (172 26 (:REWRITE DEFAULT-<-2))
     (132 44 (:REWRITE UNIT-PP-0_E))
     (124 26 (:REWRITE DEFAULT-<-1))
     (92 20
         (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
     (70 2 (:REWRITE SIZE-<-SIZE-**_E))
     (68 68 (:TYPE-PRESCRIPTION IRREDUCIBLE-PP))
     (40 24 (:LINEAR SIZE-**_E))
     (28 12 (:REWRITE ZERO-DIVISOR-LAW-FOR-**_E))
     (24 8 (:REWRITE PROJECTION-LAWS))
     (22 22 (:REWRITE |1_E-0_E|))
     (16 8 (:REWRITE GREATEST-DIVIDES-PP=0_E))
     (6 6
        (:REWRITE CLOSURE-LAWS-FOR-++_E-&-**_E))
     (2 2
        (:REWRITE ASSOCIATIVITY-LAWS-FOR-++_E-&-**_E))
     (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP)))
(SIZE-<-SIZE-*_E (2706 998 (:REWRITE EQUIVALENCE-LAW))
                 (2389 1 (:REWRITE DIVIDES-PP-<=-SIZE))
                 (1141 1 (:REWRITE DIVIDES-PP-SUFF))
                 (664 1 (:DEFINITION DIVIDES-PP))
                 (581 1 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
                 (198 1
                      (:REWRITE DIVIDES-PP-IMPLIES-RR_E=0-LEMMA-1))
                 (90 1
                     (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
                 (15 3 (:REWRITE CLOSURE-OF-QQ_E-&-RR_E))
                 (14 1 (:REWRITE DEFAULT-<-2))
                 (8 2
                    (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
                 (7 1
                    (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                 (6 6 (:TYPE-PRESCRIPTION DIVIDES-PP))
                 (6 3
                    (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
                 (4 1 (:REWRITE DEFAULT-<-1))
                 (2 2
                    (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
                 (2 1 (:REWRITE RIGHT-UNICITY-LAWS))
                 (2 1 (:REWRITE NULLITY-LAWS))
                 (2 1
                    (:REWRITE DIVIDES-PP-IMPLIES-WITNESS=QQ_E))
                 (2 1 (:REWRITE DIVIDES-P-IMPLIES-RR_E=0))
                 (1 1 (:REWRITE TRANSITIVITY-DIVIDES-PP)))
(IRREDUCIBLE-FACTORS (26140 1726
                            (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
                     (18618 174 (:REWRITE REDUCIBLE-P-SUFF))
                     (16435 11516
                            (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
                     (1296 477 (:LINEAR SIZE->=-SIZE-1_E))
                     (835 37 (:REWRITE DIVIDES-PP-<=-SIZE))
                     (476 64 (:REWRITE DEFAULT-<-2))
                     (464 37 (:REWRITE DIVIDES-PP-SUFF))
                     (347 64 (:REWRITE DEFAULT-<-1))
                     (236 32
                          (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                     (174 174 (:REWRITE REDUCIBLE-P-SUFF-2))
                     (167 37 (:DEFINITION DIVIDES-PP))
                     (135 135 (:REWRITE |1_E-0_E|))
                     (93 37 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
                     (73 73 (:TYPE-PRESCRIPTION DIVIDES-PP))
                     (73 22 (:REWRITE PROJECTION-LAWS))
                     (72 36
                         (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
                     (42 21
                         (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
                     (37 37 (:REWRITE TRANSITIVITY-DIVIDES-PP))
                     (29 22 (:REWRITE RIGHT-UNICITY-LAWS))
                     (29 22 (:REWRITE NULLITY-LAWS))
                     (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP)))
(TRUE-LISTP-IRREDUCIBLE-FACTORS-1)
(TRUE-LISTP-IRREDUCIBLE-FACTORS)
(IRREDUCIBLE-LISTP-1)
(IRREDUCIBLE-LISTP)
(IRREDUCIBLE-LISTP-1-APPEND (19 16 (:REWRITE DEFAULT-CAR))
                            (18 9
                                (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
                            (16 13 (:REWRITE DEFAULT-CDR))
                            (9 9 (:TYPE-PRESCRIPTION TRUE-LISTP))
                            (9 9 (:TYPE-PRESCRIPTION BINARY-APPEND)))
(IRREDUCIBLE-LISTP-APPEND (19 16 (:REWRITE DEFAULT-CAR))
                          (18 9
                              (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
                          (16 13 (:REWRITE DEFAULT-CDR))
                          (9 9 (:TYPE-PRESCRIPTION TRUE-LISTP))
                          (9 9 (:TYPE-PRESCRIPTION BINARY-APPEND)))
(SIZE-IMPLIES-IRREDUCIBLE-PP
     (86 62 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
     (62 62 (:TYPE-PRESCRIPTION NATP-SIZE))
     (6 2
        (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (4 4
        (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
     (2 2 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
     (2 2 (:REWRITE REDUCIBLE-PP-SUFF)))
(SIZE-IMPLIES-IRREDUCIBLE-P (562 202 (:REWRITE EQUIVALENCE-LAW))
                            (558 2 (:REWRITE REDUCIBLE-P-SUFF))
                            (378 378 (:REWRITE CLOSURE-LAWS))
                            (266 2 (:REWRITE ZERO-DIVISOR-LAW))
                            (218 18
                                 (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
                            (86 62 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
                            (62 62 (:TYPE-PRESCRIPTION NATP-SIZE))
                            (2 2 (:REWRITE REDUCIBLE-P-SUFF-2)))
(IRREDUCIBLE-LISTP-1-IRREDUCIBLE-FACTORS-1
     (150 150 (:TYPE-PRESCRIPTION NATP-SIZE))
     (118 28 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
     (75 15 (:DEFINITION BINARY-APPEND))
     (56 56
         (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
     (48 28
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (45 45 (:REWRITE DEFAULT-CDR))
     (43 43 (:REWRITE DEFAULT-CAR))
     (28 28 (:REWRITE REDUCIBLE-PP-SUFF))
     (6 2
        (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
     (2 2 (:TYPE-PRESCRIPTION BINARY-APPEND)))
(IRREDUCIBLE-LISTP-IRREDUCIBLE-FACTORS
     (7874 28 (:REWRITE REDUCIBLE-P-SUFF))
     (3672 371
           (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (3320 18 (:REWRITE ZERO-DIVISOR-LAW))
     (329 224 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
     (73 15 (:DEFINITION BINARY-APPEND))
     (47 47
         (:TYPE-PRESCRIPTION TRUE-LISTP-IRREDUCIBLE-FACTORS))
     (45 45 (:REWRITE DEFAULT-CDR))
     (43 43 (:REWRITE DEFAULT-CAR))
     (28 28 (:REWRITE REDUCIBLE-P-SUFF-2))
     (22 8 (:LINEAR SIZE->=-SIZE-1_E))
     (6 2
        (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
     (2 2 (:TYPE-PRESCRIPTION BINARY-APPEND))
     (2 2 (:REWRITE |1_E-0_E|)))
(EDP-LISTP)
(IRREDUCIBLE-LISTP-1-IMPLIES-EDP-LISTP
     (557 50 (:REWRITE DIVIDES-PP-SUFF))
     (557 44 (:REWRITE UNIT-PP-**_E-INVERSE))
     (303 29
          (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
     (148 4 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
     (112 50 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (100 100 (:REWRITE CLOSURE-LAWS))
     (93 31
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (71 71 (:TYPE-PRESCRIPTION DIVIDES-PP))
     (62 62
         (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
     (57 5
         (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
     (50 50 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (48 48 (:TYPE-PRESCRIPTION UNIT-PP))
     (31 31 (:REWRITE RIGHT-UNICITY-LAWS))
     (31 31 (:REWRITE NULLITY-LAWS))
     (30 30 (:REWRITE DEFAULT-CAR))
     (28 18 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
     (18 18 (:TYPE-PRESCRIPTION NATP-SIZE))
     (8 8 (:REWRITE DEFAULT-CDR))
     (6 2 (:LINEAR SIZE->=-SIZE-1_E))
     (4 4 (:REWRITE REDUCIBLE-PP-SUFF)))
(IRREDUCIBLE-LISTP-IMPLIES-EDP-LISTP
     (71904 22616 (:REWRITE EQUIVALENCE-LAW))
     (51592 404 (:REWRITE ZERO-DIVISOR-LAW))
     (50400 50400 (:REWRITE CLOSURE-LAWS))
     (39952 52 (:REWRITE DIVIDES-P-SUFF))
     (21604 4 (:REWRITE REDUCIBLE-P-SUFF))
     (11597 370 (:DEFINITION UNIT-PP))
     (9929 36 (:DEFINITION IRREDUCIBLE-PP))
     (9569 664 (:REWRITE DIVIDES-PP-SUFF))
     (8585 362 (:DEFINITION DIVIDES-PP))
     (7825 572 (:REWRITE UNIT-PP-**_E-INVERSE))
     (7060 7060
           (:EQUIVALENCE ==_E-EQUIVALENCE-LAW))
     (6008 36 (:DEFINITION REDUCIBLE-PP))
     (5088 96
           (:REWRITE DIVIDES-PP-IMPLIES-WITNESS=QQ_E))
     (3363 346
           (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
     (1500 664
           (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (1386 36 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
     (1296 52
           (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (1174 1174 (:TYPE-PRESCRIPTION DIVIDES-PP))
     (1110 370
           (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (740 740
          (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
     (664 664 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (645 645
          (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
     (528 528 (:TYPE-PRESCRIPTION UNIT-PP))
     (486 486 (:REWRITE DEFAULT-CAR))
     (466 466 (:REWRITE RIGHT-UNICITY-LAWS))
     (466 466 (:REWRITE NULLITY-LAWS))
     (452 36
          (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
     (252 162 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
     (176 176 (:REWRITE DEFAULT-CDR))
     (162 162 (:TYPE-PRESCRIPTION NATP-SIZE))
     (57 5 (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-P))
     (54 18 (:LINEAR SIZE->=-SIZE-1_E))
     (40 40 (:TYPE-PRESCRIPTION UNIT-P))
     (36 36 (:REWRITE REDUCIBLE-PP-SUFF))
     (36 20 (:REWRITE LEFT-UNICITY-LAWS))
     (4 4 (:REWRITE REDUCIBLE-P-SUFF-2)))
(EDP-LISTP-IRREDUCIBLE-FACTORS-1)
(EDP-LISTP-IRREDUCIBLE-FACTORS)
(**_E-LST)
(*_E-LST)
(EDP-**_E-LST (9 9 (:REWRITE DEFAULT-CAR))
              (2 2 (:REWRITE DEFAULT-CDR)))
(EDP-*_E-LST (9 9 (:REWRITE DEFAULT-CAR))
             (2 2 (:REWRITE DEFAULT-CDR)))
(**_E-LST-APPEND (49 40 (:REWRITE DEFAULT-CAR))
                 (28 14
                     (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
                 (19 16 (:REWRITE DEFAULT-CDR))
                 (14 14 (:TYPE-PRESCRIPTION TRUE-LISTP))
                 (14 14 (:TYPE-PRESCRIPTION BINARY-APPEND)))
(*_E-LST-=-**_E-LST (16 16 (:REWRITE DEFAULT-CAR))
                    (4 4 (:REWRITE DEFAULT-CDR)))
(*_E-LST-APPEND (206 2 (:REWRITE ZERO-DIVISOR-LAW))
                (48 6 (:DEFINITION **_E-LST))
                (28 28 (:REWRITE DEFAULT-CAR))
                (16 16 (:REWRITE DEFAULT-CDR))
                (16 8
                    (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
                (12 4 (:DEFINITION BINARY-APPEND))
                (8 8 (:TYPE-PRESCRIPTION TRUE-LISTP))
                (8 8 (:TYPE-PRESCRIPTION BINARY-APPEND)))
(**_E-LST-IRREDUCIBLE-FACTORS-1
     (349 349 (:TYPE-PRESCRIPTION NATP-SIZE))
     (70 70
         (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
     (25 25 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
     (25 25 (:REWRITE DEFAULT-CAR))
     (16 4 (:LINEAR SIZE->=-SIZE-1_E))
     (15 3 (:DEFINITION BINARY-APPEND))
     (14 14 (:REWRITE DEFAULT-CDR))
     (13 5 (:REWRITE UNIT-PP-0_E)))
(RIGHT-UNICITY-LAW-FOR-*_E)
(*_E-CONGRUENCE (19009 106 (:REWRITE ZERO-DIVISOR-LAW)))
(*_E-LST-IRREDUCIBLE-FACTORS
     (1835 1329
           (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
     (592 592
          (:TYPE-PRESCRIPTION TRUE-LISTP-IRREDUCIBLE-FACTORS))
     (500 100 (:DEFINITION BINARY-APPEND))
     (432 144
          (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
     (358 358 (:REWRITE DEFAULT-CAR))
     (229 229 (:REWRITE DEFAULT-CDR))
     (144 144 (:TYPE-PRESCRIPTION BINARY-APPEND))
     (110 40 (:LINEAR SIZE->=-SIZE-1_E))
     (84 84 (:REWRITE REDUCIBLE-P-SUFF-2))
     (10 10 (:REWRITE |1_E-0_E|)))
(IRREDUCIBLE-FACTORIZATION-EXISTENCE
     (1782 642 (:REWRITE EQUIVALENCE-LAW))
     (1769 1 (:DEFINITION IRREDUCIBLE-FACTORS))
     (1487 1 (:DEFINITION REDUCIBLE-P))
     (1145 1145 (:REWRITE CLOSURE-LAWS))
     (1080 5 (:REWRITE ZERO-DIVISOR-LAW))
     (407 11
          (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (207 1 (:REWRITE REDUCIBLE-P-SUFF))
     (24 16 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
     (16 16 (:TYPE-PRESCRIPTION NATP-SIZE))
     (14 14 (:EQUIVALENCE ==_E-EQUIVALENCE-LAW))
     (11 4 (:LINEAR SIZE->=-SIZE-1_E))
     (8 4 (:DEFINITION MV-NTH))
     (6 1 (:DEFINITION *_E-LST))
     (5 5 (:REWRITE DEFAULT-CAR))
     (5 1 (:DEFINITION BINARY-APPEND))
     (4 4 (:REWRITE DEFAULT-CDR))
     (1 1 (:REWRITE REDUCIBLE-P-SUFF-2))
     (1 1 (:REWRITE |1_E-0_E|)))
(GCD-P)
(GCD-P-NECC)
(GCD-PP-WITNESS)
(==_E-IMPLIES-==_E-GCD-PP-WITNESS-1)
(==_E-IMPLIES-==_E-GCD-PP-WITNESS-2)
(==_E-IMPLIES-==_E-GCD-PP-WITNESS-3)
(GCD-PP)
(==_E-IMPLIES-EQUAL-GCD-PP-1
     (206 20 (:REWRITE DIVIDES-PP-SUFF))
     (148 10
          (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
     (40 20 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (32 32 (:REWRITE CLOSURE-LAWS))
     (30 30 (:TYPE-PRESCRIPTION DIVIDES-PP))
     (20 20 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (18 18
         (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
     (10 10 (:REWRITE RIGHT-UNICITY-LAWS))
     (10 10 (:REWRITE NULLITY-LAWS))
     (6 2 (:REWRITE PROJECTION-LAWS)))
(==_E-IMPLIES-EQUAL-GCD-PP-2
     (206 20 (:REWRITE DIVIDES-PP-SUFF))
     (148 10
          (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
     (40 20 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (32 32 (:REWRITE CLOSURE-LAWS))
     (30 30 (:TYPE-PRESCRIPTION DIVIDES-PP))
     (20 20 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (18 18
         (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
     (10 10 (:REWRITE RIGHT-UNICITY-LAWS))
     (10 10 (:REWRITE NULLITY-LAWS))
     (6 2 (:REWRITE PROJECTION-LAWS)))
(==_E-IMPLIES-EQUAL-GCD-PP-3
     (206 20 (:REWRITE DIVIDES-PP-SUFF))
     (148 10
          (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
     (40 20 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (32 32 (:REWRITE CLOSURE-LAWS))
     (30 30 (:TYPE-PRESCRIPTION DIVIDES-PP))
     (20 20 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (18 18
         (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
     (10 10 (:REWRITE RIGHT-UNICITY-LAWS))
     (10 10 (:REWRITE NULLITY-LAWS))
     (6 2 (:REWRITE PROJECTION-LAWS)))
(GCD-P-NECC-1 (5 5 (:REWRITE DIVIDES-P-SUFF))
              (1 1 (:REWRITE GCD-P-NECC)))
(GCD-PP-NECC-LEMMA-1 (15 7 (:REWRITE TRANSITIVITY-DIVIDES-PP))
                     (7 7 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
                     (7 7 (:REWRITE DIVIDES-PP-SUFF))
                     (5 5 (:REWRITE DIVIDES-P-SUFF))
                     (1 1 (:REWRITE GCD-P-NECC-1))
                     (1 1 (:REWRITE GCD-P-NECC)))
(GCD-PP-NECC-LEMMA-2 (25 11 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
                     (3 3 (:REWRITE NULLITY-LAWS))
                     (2 2 (:REWRITE DIVIDES-P-SUFF)))
(GCD-PP-NECC (444 172 (:REWRITE TRANSITIVITY-DIVIDES-PP))
             (172 172
                  (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
             (172 172 (:REWRITE DIVIDES-PP-SUFF))
             (29 29 (:REWRITE DIVIDES-P-SUFF)))
(GCD-P-IMPLIES-GCD-PP (33 33 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
                      (31 31 (:REWRITE DIVIDES-PP-SUFF))
                      (4 4 (:REWRITE GCD-P-NECC-1))
                      (4 4 (:REWRITE GCD-P-NECC))
                      (3 3 (:REWRITE GCD-PP-NECC)))
(GCD-PP-IMPLIES-GCD-P (33 33 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
                      (31 31 (:REWRITE DIVIDES-PP-SUFF))
                      (14 14 (:REWRITE DIVIDES-P-SUFF))
                      (4 4 (:REWRITE GCD-PP-NECC))
                      (3 3 (:REWRITE GCD-P-NECC-1))
                      (3 3 (:REWRITE GCD-P-NECC)))
(GCD-P-=-GCD-PP (1 1 (:REWRITE GCD-PP-NECC))
                (1 1 (:REWRITE GCD-P-NECC-1))
                (1 1 (:REWRITE GCD-P-NECC)))
(BEZOUT1-PROPERTY (262 262 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
                  (262 262 (:TYPE-PRESCRIPTION NATP-SIZE))
                  (9 9 (:REWRITE DEFAULT-CDR))
                  (7 7 (:REWRITE DEFAULT-CAR))
                  (4 4 (:REWRITE DEFAULT-<-2))
                  (4 4 (:REWRITE DEFAULT-<-1)))
(BEZOUT1-PROPERTIES-SIZE (425 425 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
                         (425 425 (:TYPE-PRESCRIPTION NATP-SIZE))
                         (16 4 (:REWRITE |1_E-0_E|))
                         (11 11 (:REWRITE DEFAULT-CDR))
                         (11 11 (:REWRITE DEFAULT-CAR))
                         (4 4 (:REWRITE CLOSURE-LAWS)))
(BEZOUT1-PROPERTIES-SIZE-1_E-0_E (201 201 (:TYPE-PRESCRIPTION NATP-SIZE))
                                 (12 4 (:REWRITE BEZOUT1-PROPERTY))
                                 (11 11 (:REWRITE DEFAULT-CDR))
                                 (11 11 (:REWRITE DEFAULT-CAR)))
(FIND-SMALLEST-N (123 123 (:TYPE-PRESCRIPTION NATP-SIZE))
                 (55 32 (:REWRITE DEFAULT-<-1))
                 (46 33 (:REWRITE DEFAULT-+-1))
                 (35 33 (:REWRITE DEFAULT-+-2))
                 (35 32 (:REWRITE DEFAULT-<-2))
                 (16 1 (:REWRITE <-+-NEGATIVE-0-2))
                 (14 2
                     (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                 (10 2
                     (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
                 (5 5 (:REWRITE DEFAULT-UNARY-MINUS))
                 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
                 (3 3 (:REWRITE DEFAULT-CDR))
                 (3 3 (:REWRITE DEFAULT-CAR))
                 (3 3 (:REWRITE BEZOUT1-PROPERTY)))
(INTEGERP-FIND-SMALLEST-N)
(NATP-FIND-SMALLEST-N (217 217 (:TYPE-PRESCRIPTION NATP-SIZE))
                      (139 71 (:REWRITE DEFAULT-<-1))
                      (87 71 (:REWRITE DEFAULT-<-2))
                      (44 44 (:REWRITE DEFAULT-CDR))
                      (44 44 (:REWRITE DEFAULT-CAR))
                      (36 36 (:REWRITE BEZOUT1-PROPERTY))
                      (18 6 (:REWRITE COMMUTATIVITY-OF-+))
                      (14 2
                          (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                      (12 12 (:REWRITE DEFAULT-+-2))
                      (12 12 (:REWRITE DEFAULT-+-1)))
(FIND-SMALLEST-N-SIZE-X (1591 1591 (:TYPE-PRESCRIPTION NATP-SIZE))
                        (352 205 (:REWRITE DEFAULT-<-1))
                        (344 205 (:REWRITE DEFAULT-<-2))
                        (113 35
                             (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                        (69 69 (:REWRITE DEFAULT-CDR))
                        (69 69 (:REWRITE DEFAULT-CAR))
                        (50 50 (:REWRITE DEFAULT-+-2))
                        (50 50 (:REWRITE DEFAULT-+-1))
                        (30 10 (:REWRITE FOLD-CONSTS-IN-+))
                        (10 10 (:REWRITE EQUAL-CONSTANT-+)))
(BEZOUT1-FIND-SMALLEST-N (1748 1748 (:TYPE-PRESCRIPTION NATP-SIZE))
                         (914 654 (:REWRITE DEFAULT-<-2))
                         (694 654 (:REWRITE DEFAULT-<-1))
                         (626 626 (:REWRITE DEFAULT-+-2))
                         (626 626 (:REWRITE DEFAULT-+-1))
                         (336 112 (:REWRITE FOLD-CONSTS-IN-+))
                         (112 112 (:REWRITE EQUAL-CONSTANT-+))
                         (40 4 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
                         (20 4
                             (:REWRITE DIVIDES-PP-IMPLIES-RR_E=0-LEMMA-1))
                         (10 1
                             (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                         (8 4
                            (:REWRITE DIVIDES-PP-IMPLIES-WITNESS=QQ_E))
                         (8 4 (:REWRITE DIVIDES-P-IMPLIES-RR_E=0))
                         (4 4 (:REWRITE TRANSITIVITY-DIVIDES-PP)))
(NOT-SIZE-BEZOUT1-N-=-N (4983 4983 (:TYPE-PRESCRIPTION NATP-SIZE))
                        (484 303 (:REWRITE DEFAULT-<-2))
                        (303 303 (:REWRITE DEFAULT-<-1))
                        (278 245 (:REWRITE DEFAULT-CAR))
                        (238 238 (:REWRITE DEFAULT-CDR))
                        (180 180 (:REWRITE DEFAULT-+-2))
                        (180 180 (:REWRITE DEFAULT-+-1))
                        (90 30 (:REWRITE FOLD-CONSTS-IN-+))
                        (30 30 (:REWRITE EQUAL-CONSTANT-+))
                        (3 1 (:REWRITE NATP-SIZE-==_E))
                        (2 1 (:REWRITE NATP-SIZE))
                        (1 1 (:REWRITE BEZOUT1-PROPERTIES-SIZE)))
(NATP-FIND-SMALLEST-N-0)
(BEZOUT1-FIND-SMALLEST-N-0 (22 22 (:TYPE-PRESCRIPTION NATP-SIZE)))
(NOT-SIZE-BEZOUT1-N-=-N-1)
(SIZE->=-FIND-SMALLEST-N-0 (394 394 (:TYPE-PRESCRIPTION NATP-SIZE))
                           (51 18 (:REWRITE DEFAULT-<-1))
                           (35 18 (:REWRITE DEFAULT-<-2))
                           (19 5
                               (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
                           (7 7 (:REWRITE NOT-SIZE-BEZOUT1-N-=-N)))
(EQUATION-0)
(EQUATION-1)
(EQUATION-2 (35 4 (:REWRITE DIVIDES-P-IMPLIES-RR_E=0))
            (16 1 (:REWRITE DIVIDES-PP-SUFF))
            (10 1 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
            (8 4
               (:REWRITE DIVIDES-PP-IMPLIES-RR_E=0-LEMMA-1))
            (4 4 (:TYPE-PRESCRIPTION DIVIDES-PP))
            (4 1 (:DEFINITION DIVIDES-PP))
            (3 1 (:REWRITE PROJECTION-LAWS))
            (2 2 (:REWRITE CLOSURE-LAWS))
            (2 1
               (:REWRITE DIVIDES-PP-IMPLIES-WITNESS=QQ_E))
            (2 1
               (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
            (1 1 (:REWRITE TRANSITIVITY-DIVIDES-PP))
            (1 1 (:REWRITE RIGHT-UNICITY-LAWS))
            (1 1 (:REWRITE NULLITY-LAWS))
            (1 1
               (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E)))
(EQUATION-3 (632 108
                 (:REWRITE INVERSE-CANCELLATION-LAWS-**_E))
            (460 4 (:REWRITE DIVIDES-P-IMPLIES-RR_E=0))
            (268 2 (:REWRITE DIVIDES-PP-SUFF))
            (152 2 (:DEFINITION DIVIDES-PP))
            (132 40
                 (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
            (34 2 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
            (16 2 (:REWRITE COMMUTATIVITY-2-LAWS))
            (12 4 (:REWRITE RIGHT-UNICITY-LAWS))
            (12 4
                (:REWRITE DIVIDES-PP-IMPLIES-RR_E=0-LEMMA-1))
            (12 2 (:REWRITE NULLITY-LAWS))
            (8 8 (:TYPE-PRESCRIPTION DIVIDES-PP))
            (6 6 (:REWRITE CLOSURE-LAWS))
            (4 2
               (:REWRITE DIVIDES-PP-IMPLIES-WITNESS=QQ_E))
            (4 2
               (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
            (2 2 (:REWRITE TRANSITIVITY-DIVIDES-PP)))
(EQUATION-3A (632 108
                  (:REWRITE INVERSE-CANCELLATION-LAWS-**_E))
             (460 4 (:REWRITE DIVIDES-P-IMPLIES-RR_E=0))
             (268 2 (:REWRITE DIVIDES-PP-SUFF))
             (152 2 (:DEFINITION DIVIDES-PP))
             (132 40
                  (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
             (34 2 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
             (16 2 (:REWRITE COMMUTATIVITY-2-LAWS))
             (12 4 (:REWRITE RIGHT-UNICITY-LAWS))
             (12 4
                 (:REWRITE DIVIDES-PP-IMPLIES-RR_E=0-LEMMA-1))
             (12 2 (:REWRITE NULLITY-LAWS))
             (8 8 (:TYPE-PRESCRIPTION DIVIDES-PP))
             (6 6 (:REWRITE CLOSURE-LAWS))
             (4 2
                (:REWRITE DIVIDES-PP-IMPLIES-WITNESS=QQ_E))
             (4 2
                (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
             (2 2 (:REWRITE TRANSITIVITY-DIVIDES-PP)))
(INEQUALITY-4 (892 132
                   (:REWRITE INVERSE-CANCELLATION-LAWS-**_E))
              (467 3 (:REWRITE DIVIDES-P-IMPLIES-RR_E=0))
              (292 3 (:REWRITE DIVIDES-PP-SUFF))
              (228 3 (:DEFINITION DIVIDES-PP))
              (188 54
                   (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
              (104 3
                   (:REWRITE DIVIDES-PP-IMPLIES-RR_E=0-LEMMA-1))
              (97 2
                  (:REWRITE DIVIDES-PP-IMPLIES-WITNESS=QQ_E))
              (34 34 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
              (34 34 (:TYPE-PRESCRIPTION NATP-SIZE))
              (33 3 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
              (16 2 (:REWRITE COMMUTATIVITY-2-LAWS))
              (14 1 (:REWRITE DEFAULT-<-1))
              (12 4 (:REWRITE RIGHT-UNICITY-LAWS))
              (12 2 (:REWRITE NULLITY-LAWS))
              (8 8 (:TYPE-PRESCRIPTION DIVIDES-PP))
              (8 8 (:REWRITE CLOSURE-LAWS))
              (7 1
                 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
              (6 3
                 (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
              (3 3 (:REWRITE TRANSITIVITY-DIVIDES-PP))
              (2 1 (:REWRITE DEFAULT-<-2)))
(INEQUALITY-4A (892 132
                    (:REWRITE INVERSE-CANCELLATION-LAWS-**_E))
               (467 3 (:REWRITE DIVIDES-P-IMPLIES-RR_E=0))
               (292 3 (:REWRITE DIVIDES-PP-SUFF))
               (228 3 (:DEFINITION DIVIDES-PP))
               (188 54
                    (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
               (104 3
                    (:REWRITE DIVIDES-PP-IMPLIES-RR_E=0-LEMMA-1))
               (97 2
                   (:REWRITE DIVIDES-PP-IMPLIES-WITNESS=QQ_E))
               (34 34 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
               (34 34 (:TYPE-PRESCRIPTION NATP-SIZE))
               (33 3 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
               (16 2 (:REWRITE COMMUTATIVITY-2-LAWS))
               (14 1 (:REWRITE DEFAULT-<-1))
               (12 4 (:REWRITE RIGHT-UNICITY-LAWS))
               (12 2 (:REWRITE NULLITY-LAWS))
               (8 8 (:TYPE-PRESCRIPTION DIVIDES-PP))
               (8 8 (:REWRITE CLOSURE-LAWS))
               (7 1
                  (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
               (6 3
                  (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
               (3 3 (:REWRITE TRANSITIVITY-DIVIDES-PP))
               (2 1 (:REWRITE DEFAULT-<-2)))
(EQUATION-5 (86 36
                (:REWRITE INVERSE-CANCELLATION-LAWS-**_E)))
(EQUATION-5A (86 36
                 (:REWRITE INVERSE-CANCELLATION-LAWS-**_E)))
(EQUATION-6 (396 48
                 (:REWRITE INVERSE-CANCELLATION-LAWS-**_E))
            (84 12
                (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E)))
(EQUATION-6A (396 48
                  (:REWRITE INVERSE-CANCELLATION-LAWS-**_E)))
(INEQUALITY-7 (756 60
                   (:REWRITE INVERSE-CANCELLATION-LAWS-**_E))
              (168 24
                   (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
              (74 74 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
              (74 74 (:TYPE-PRESCRIPTION NATP-SIZE))
              (20 2 (:REWRITE DEFAULT-<-1))
              (10 2
                  (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
              (4 2 (:REWRITE DEFAULT-<-2)))
(INEQUALITY-7A (756 60
                    (:REWRITE INVERSE-CANCELLATION-LAWS-**_E))
               (168 24
                    (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
               (74 74 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
               (74 74 (:TYPE-PRESCRIPTION NATP-SIZE))
               (20 2 (:REWRITE DEFAULT-<-1))
               (10 2
                   (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
               (4 2 (:REWRITE DEFAULT-<-2)))
(EQUATION-8 (930 60
                 (:REWRITE INVERSE-CANCELLATION-LAWS-**_E))
            (210 30
                 (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
            (52 52 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
            (52 52 (:TYPE-PRESCRIPTION NATP-SIZE))
            (28 2 (:REWRITE DEFAULT-<-1))
            (14 2
                (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
            (4 2 (:REWRITE DEFAULT-<-2)))
(EQUATION-8A (930 60
                  (:REWRITE INVERSE-CANCELLATION-LAWS-**_E))
             (52 52 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
             (52 52 (:TYPE-PRESCRIPTION NATP-SIZE))
             (28 2 (:REWRITE DEFAULT-<-1))
             (14 2
                 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
             (4 2 (:REWRITE DEFAULT-<-2)))
(DIVIDES-PP-BEZOUT1-X (632 108
                           (:REWRITE INVERSE-CANCELLATION-LAWS-**_E))
                      (6 2 (:REWRITE RIGHT-UNICITY-LAWS))
                      (6 1 (:REWRITE NULLITY-LAWS))
                      (4 1
                         (:REWRITE DIVIDES-PP-IMPLIES-RR_E=0-LEMMA-1))
                      (3 3 (:REWRITE CLOSURE-LAWS))
                      (2 2 (:REWRITE TRANSITIVITY-DIVIDES-PP))
                      (1 1
                         (:REWRITE DIVIDES-PP-IMPLIES-WITNESS=QQ_E))
                      (1 1
                         (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS)))
(DIVIDES-PP-BEZOUT1-Y (632 108
                           (:REWRITE INVERSE-CANCELLATION-LAWS-**_E))
                      (6 2 (:REWRITE RIGHT-UNICITY-LAWS))
                      (6 1 (:REWRITE NULLITY-LAWS))
                      (4 1
                         (:REWRITE DIVIDES-PP-IMPLIES-RR_E=0-LEMMA-1))
                      (3 3 (:REWRITE CLOSURE-LAWS))
                      (2 2 (:REWRITE TRANSITIVITY-DIVIDES-PP))
                      (1 1
                         (:REWRITE DIVIDES-PP-IMPLIES-WITNESS=QQ_E))
                      (1 1
                         (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS)))
(BEZOUT)
(EDP-MV-NTH-BEZOUT)
(GCD-PP-MV-NTH-BEZOUT (33 19 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
                      (16 16 (:REWRITE TRANSITIVITY-DIVIDES-PP))
                      (9 9
                         (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
                      (3 3 (:REWRITE GCD-PP-NECC)))
(NTH-MV-NTH (6 6 (:REWRITE ZP-OPEN))
            (6 6 (:REWRITE DEFAULT-CAR))
            (4 4 (:REWRITE DEFAULT-CDR))
            (4 4 (:REWRITE DEFAULT-+-2))
            (4 4 (:REWRITE DEFAULT-+-1)))
(GCD-PP-NTH-BEZOUT (33 19 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
                   (16 16 (:REWRITE TRANSITIVITY-DIVIDES-PP))
                   (9 9
                      (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
                   (3 3 (:REWRITE GCD-PP-NECC)))
(1ST-2ND-MV-NTH)
(GCD-PP-BEZOUT (33 19 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
               (16 16 (:REWRITE TRANSITIVITY-DIVIDES-PP))
               (9 9
                  (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
               (3 3 (:REWRITE GCD-PP-NECC)))
(COMMON-DIVISOR-MV-NTH-BEZOUT
     (28 5 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (15 5 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (6 6
        (:REWRITE CLOSURE-LAWS-FOR-++_E-&-**_E))
     (6 3 (:DEFINITION DIVIDES-PP))
     (2 1
        (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS)))
(GREATEST-COMMON-DIVISOR-MV-NTH-BEZOUT
     (32 3
         (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
     (29 7 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (18 10 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (8 8 (:REWRITE CLOSURE-LAWS))
     (3 3 (:REWRITE RIGHT-UNICITY-LAWS))
     (3 3 (:REWRITE NULLITY-LAWS))
     (1 1
        (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E)))
(GCD-PP-ASSOCIATES-PP (6482 368
                            (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
                      (1763 883
                            (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
                      (1118 1118 (:REWRITE CLOSURE-LAWS))
                      (883 883 (:REWRITE TRANSITIVITY-DIVIDES-PP))
                      (368 368 (:REWRITE RIGHT-UNICITY-LAWS))
                      (368 368 (:REWRITE NULLITY-LAWS))
                      (141 141 (:REWRITE GCD-PP-NECC)))
(GCD-PP-EDP-1 (25 9 (:REWRITE TRANSITIVITY-DIVIDES-PP))
              (9 9 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
              (9 9 (:REWRITE DIVIDES-PP-SUFF))
              (1 1 (:REWRITE GCD-PP-NECC)))
(GCD-PP-EDP-2 (25 9 (:REWRITE TRANSITIVITY-DIVIDES-PP))
              (9 9 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
              (9 9 (:REWRITE DIVIDES-PP-SUFF))
              (1 1 (:REWRITE GCD-PP-NECC)))
(GCD-PP-EDP-3 (1 1 (:REWRITE TRANSITIVITY-DIVIDES-PP))
              (1 1 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
              (1 1 (:REWRITE GCD-PP-NECC))
              (1 1 (:REWRITE DIVIDES-PP-SUFF)))
(GCD=LINEAR-COMBINATION (344 22
                             (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
                        (214 66
                             (:REWRITE INVERSE-CANCELLATION-LAWS-**_E))
                        (105 52 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
                        (71 71 (:REWRITE CLOSURE-LAWS))
                        (52 52 (:REWRITE TRANSITIVITY-DIVIDES-PP))
                        (45 3 (:REWRITE COMMUTATIVITY-2-LAWS))
                        (33 11 (:REWRITE PROJECTION-LAWS))
                        (27 23 (:REWRITE RIGHT-UNICITY-LAWS))
                        (27 22 (:REWRITE NULLITY-LAWS))
                        (9 9 (:REWRITE GCD-PP-NECC)))
(ASSOCIATES-PP-IMPLIES-EQUAL-GCD-PP-1
     (1995 683 (:REWRITE DIVIDES-PP-SUFF))
     (1018 1018
           (:EQUIVALENCE ==_E-EQUIVALENCE-LAW))
     (920 726
          (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (196 196 (:REWRITE CLOSURE-LAWS))
     (127 127 (:REWRITE GCD-PP-NECC))
     (120 40 (:REWRITE PROJECTION-LAWS))
     (98 98 (:REWRITE RIGHT-UNICITY-LAWS))
     (98 98 (:REWRITE NULLITY-LAWS))
     (56 56
         (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
     (20 20 (:REWRITE GCD-PP-ASSOCIATES-PP)))
(ASSOCIATES-PP-IMPLIES-IFF-GCD-PP-2
     (1714 861 (:REWRITE DIVIDES-PP-SUFF))
     (1054 934
           (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (656 656 (:EQUIVALENCE ==_E-EQUIVALENCE-LAW))
     (154 154 (:REWRITE GCD-PP-NECC))
     (124 124 (:REWRITE CLOSURE-LAWS))
     (120 40 (:REWRITE PROJECTION-LAWS))
     (62 62 (:REWRITE RIGHT-UNICITY-LAWS))
     (62 62 (:REWRITE NULLITY-LAWS))
     (29 29
         (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
     (20 20 (:REWRITE GCD-PP-ASSOCIATES-PP)))
(ASSOCIATES-PP-IMPLIES-EQUAL-GCD-PP-2)
(ASSOCIATES-PP-IMPLIES-IFF-GCD-PP-3
     (3285 902 (:REWRITE DIVIDES-PP-SUFF))
     (1880 1880
           (:EQUIVALENCE ==_E-EQUIVALENCE-LAW))
     (1400 1000
           (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (408 408 (:REWRITE CLOSURE-LAWS))
     (180 180 (:REWRITE RIGHT-UNICITY-LAWS))
     (180 180 (:REWRITE NULLITY-LAWS))
     (154 154 (:REWRITE GCD-PP-NECC))
     (120 40 (:REWRITE PROJECTION-LAWS))
     (95 95
         (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
     (20 20 (:REWRITE GCD-PP-ASSOCIATES-PP)))
(ASSOCIATES-PP-IMPLIES-EQUAL-GCD-PP-3)
(LINEAR-COMBINATION-DIVIDES-PP-GCD
     (98 2 (:REWRITE DIVIDES-PP-++_E))
     (50 4 (:REWRITE DIVIDES-PP-**_E))
     (37 15 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (26 19
         (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
     (18 14
         (:REWRITE LEFT-DISTRIBUTIVITY-LAW-FOR-++_E-&-**_E))
     (14 14
         (:REWRITE CLOSURE-LAWS-FOR-++_E-&-**_E))
     (12 12 (:REWRITE GCD-PP-NECC))
     (12 10 (:REWRITE RIGHT-DISTRIBUTIVITY-LAW))
     (8 8 (:REWRITE NULLITY-LAWS))
     (5 5 (:REWRITE DEFAULT-CDR))
     (5 5 (:REWRITE DEFAULT-CAR))
     (2 2
        (:REWRITE CANCELLATION-LAWS-FOR-**_E)))
(EDP-DIVIDES-P-WITNESS-LINEAR-COMBINATION
     (138 3
          (:REWRITE DIVIDES-PP-IMPLIES-WITNESS=QQ_E))
     (61 61 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (57 57 (:REWRITE DIVIDES-PP-SUFF))
     (6 6 (:EQUIVALENCE ==_E-EQUIVALENCE-LAW))
     (1 1 (:REWRITE GCD-PP-NECC)))
(UNIT-ASSOCIATES-P)
(UNIT-ASSOCIATES-P-SUFF)
(UNIT-ASSOCIATES-P1)
(UNIT-ASSOCIATES-P1-SUFF)
(*_E-=-**_E)
(=_E-=-==_E)
(UNIT-P-IMPLIES-EDP (1 1 (:REWRITE DIVIDES-P-SUFF)))
(UNIT-ASSOCIATES-P-IMPLIES-UNIT-ASSOCIATES-P1
     (3420 801 (:REWRITE EQUIVALENCE-LAW))
     (3311 134
           (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (1486 1486 (:REWRITE CLOSURE-LAWS))
     (14 14 (:REWRITE UNIT-ASSOCIATES-P-SUFF))
     (5 5 (:REWRITE UNIT-ASSOCIATES-P1-SUFF)))
(UNIT-ASSOCIATES-P1-IMPLIES-UNIT-ASSOCIATES-P
     (4154 1009 (:REWRITE EQUIVALENCE-LAW))
     (3171 149
           (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (1842 1824 (:REWRITE CLOSURE-LAWS))
     (706 3 (:REWRITE ZERO-DIVISOR-LAW))
     (77 44
         (:REWRITE CLOSURE-LAWS-FOR-++_E-&-**_E))
     (14 14 (:REWRITE UNIT-ASSOCIATES-P1-SUFF))
     (6 6 (:REWRITE UNIT-ASSOCIATES-P-SUFF)))
(UNIT-ASSOCIATES-P-IFF-UNIT-ASSOCIATES-P1)
(BOOLEANP-UNIT-ASSOCIATES-P (17448 5228 (:REWRITE UNIT-P-IMPLIES-EDP))
                            (16744 39 (:REWRITE ZERO-DIVISOR-LAW))
                            (409 409 (:TYPE-PRESCRIPTION UNIT-P))
                            (224 224
                                 (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
                            (169 137
                                 (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
                            (152 137 (:REWRITE DIVIDES-P-SUFF)))
(UNIT-ASSOCIATES-P-=-UNIT-ASSOCIATES-P1
     (2 2 (:REWRITE UNIT-ASSOCIATES-P1-SUFF))
     (1 1 (:REWRITE UNIT-ASSOCIATES-P-SUFF)))
(UNIT-ASSOCIATES-PP-WITNESS)
(==_E-IMPLIES-==_E-ASSOCIATES-PP-WITNESS-1)
(==_E-IMPLIES-==_E-ASSOCIATES-PP-WITNESS-2)
(UNIT-ASSOCIATES-PP)
(==_E-=-EQUAL (1834 434 (:REWRITE UNIT-P-IMPLIES-EDP))
              (1821 25 (:DEFINITION UNIT-P))
              (1811 3 (:DEFINITION DIVIDES-P))
              (1798 408 (:REWRITE EQUIVALENCE-LAW))
              (1266 6 (:REWRITE ZERO-DIVISOR-LAW))
              (794 794 (:REWRITE CLOSURE-LAWS))
              (70 70 (:TYPE-PRESCRIPTION UNIT-P))
              (44 44
                  (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
              (29 25
                  (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
              (29 25 (:REWRITE DIVIDES-P-SUFF)))
(==_E-IMPLIES-EQUAL-UNIT-ASSOCIATES-PP-1
     (37160 9097 (:REWRITE UNIT-P-IMPLIES-EDP))
     (36786 312 (:DEFINITION UNIT-P))
     (36768 8632 (:REWRITE EQUIVALENCE-LAW))
     (33577 87 (:DEFINITION DIVIDES-P))
     (27994 83 (:REWRITE ZERO-DIVISOR-LAW))
     (16782 16752 (:REWRITE CLOSURE-LAWS))
     (3860 312 (:REWRITE DIVIDES-P-SUFF))
     (1028 1028 (:TYPE-PRESCRIPTION UNIT-P))
     (692 312
          (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (450 450
          (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
     (160 12 (:REWRITE DIVIDES-PP-SUFF))
     (140 8 (:REWRITE UNIT-PP-**_E-INVERSE))
     (112 16
          (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
     (96 8
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (32 12 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (20 20 (:TYPE-PRESCRIPTION DIVIDES-PP))
     (16 16
         (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
     (12 12 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (8 8 (:TYPE-PRESCRIPTION UNIT-PP))
     (8 8 (:REWRITE RIGHT-UNICITY-LAWS))
     (8 8 (:REWRITE NULLITY-LAWS))
     (3 3 (:REWRITE RIGHT-UNICITY-LAW-FOR-*_E)))
(==_E-IMPLIES-EQUAL-UNIT-ASSOCIATES-PP-2
     (20544 4926 (:REWRITE UNIT-P-IMPLIES-EDP))
     (20298 4756 (:REWRITE EQUIVALENCE-LAW))
     (20250 233 (:DEFINITION UNIT-P))
     (15034 92 (:DEFINITION DIVIDES-P))
     (14810 62 (:REWRITE ZERO-DIVISOR-LAW))
     (9005 8977 (:REWRITE CLOSURE-LAWS))
     (5859 233 (:REWRITE DIVIDES-P-SUFF))
     (748 748 (:TYPE-PRESCRIPTION UNIT-P))
     (513 233
          (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (282 282
          (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
     (84 4
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (84 4
         (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
     (8 8
        (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
     (8 4 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (8 4 (:REWRITE DIVIDES-PP-SUFF))
     (4 4 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (2 2 (:REWRITE RIGHT-UNICITY-LAW-FOR-*_E)))
(UNIT-ASSOCIATES-PP-SUFF
     (1579 160
           (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (1326 307 (:REWRITE EQUIVALENCE-LAW))
     (723 100
          (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
     (575 575 (:REWRITE CLOSURE-LAWS))
     (561 4 (:DEFINITION IRREDUCIBLE-PP))
     (153 50
          (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (144 4 (:DEFINITION REDUCIBLE-PP))
     (86 4
         (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
     (42 27 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
     (30 4 (:REWRITE REDUCIBLE-PP-SUFF))
     (27 27 (:TYPE-PRESCRIPTION NATP-SIZE))
     (16 8 (:DEFINITION MV-NTH))
     (9 3 (:LINEAR SIZE->=-SIZE-1_E))
     (6 6 (:TYPE-PRESCRIPTION IRREDUCIBLE-PP))
     (4 4 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
     (4 4 (:REWRITE DEFAULT-CDR))
     (4 4 (:REWRITE DEFAULT-CAR)))
(UNIT-ASSOCIATES-P1-IMPLIES-UNIT-ASSOCIATES-PP
     (493 70
          (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (386 87 (:REWRITE EQUIVALENCE-LAW))
     (161 161 (:REWRITE CLOSURE-LAWS))
     (116 32
          (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
     (64 1 (:DEFINITION IRREDUCIBLE-PP))
     (57 16
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (36 1 (:DEFINITION REDUCIBLE-PP))
     (27 1
         (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
     (15 1 (:REWRITE REDUCIBLE-PP-SUFF))
     (14 9 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
     (10 10 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
     (9 9 (:TYPE-PRESCRIPTION NATP-SIZE))
     (8 4 (:REWRITE PROJECTION-LAWS))
     (5 5 (:REWRITE UNIT-ASSOCIATES-P1-SUFF))
     (4 2 (:DEFINITION MV-NTH))
     (3 3 (:TYPE-PRESCRIPTION IRREDUCIBLE-PP))
     (3 1 (:LINEAR SIZE->=-SIZE-1_E))
     (1 1 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
     (1 1 (:REWRITE DEFAULT-CDR))
     (1 1 (:REWRITE DEFAULT-CAR)))
(UNIT-ASSOCIATES-PP-IMPLIES-UNIT-ASSOCIATES-P1
     (645 65
          (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (535 121 (:REWRITE EQUIVALENCE-LAW))
     (227 227 (:REWRITE CLOSURE-LAWS))
     (22 8
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (16 16
         (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
     (10 10 (:REWRITE UNIT-ASSOCIATES-P1-SUFF))
     (5 5 (:REWRITE UNIT-ASSOCIATES-PP-SUFF)))
(UNIT-ASSOCIATES-P1-IFF-UNIT-ASSOCIATES-PP)
(UNIT-ASSOCIATES-P1-=-UNIT-ASSOCIATES-PP
     (2 2 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
     (1 1 (:REWRITE UNIT-ASSOCIATES-P1-SUFF)))
(UNIT-ASSOCIATES-P-=-UNIT-ASSOCIATES-PP)
(REFLEXIVITY-UNIT-ASSOCIATES-PP (913 216 (:REWRITE UNIT-P-IMPLIES-EDP))
                                (908 12 (:DEFINITION UNIT-P))
                                (904 1 (:DEFINITION DIVIDES-P))
                                (899 204 (:REWRITE EQUIVALENCE-LAW))
                                (633 3 (:REWRITE ZERO-DIVISOR-LAW))
                                (397 397 (:REWRITE CLOSURE-LAWS))
                                (34 34 (:TYPE-PRESCRIPTION UNIT-P))
                                (22 22
                                    (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
                                (14 12
                                    (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
                                (14 12 (:REWRITE DIVIDES-P-SUFF))
                                (1 1 (:REWRITE UNIT-ASSOCIATES-PP-SUFF)))
(SYMMETRY-UNIT-ASSOCIATES-PP
     (594 168 (:REWRITE UNIT-P-IMPLIES-EDP))
     (372 44 (:DEFINITION UNIT-P))
     (272 44 (:DEFINITION DIVIDES-P))
     (194 66
          (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
     (168 168 (:TYPE-PRESCRIPTION UNIT-P))
     (123 3 (:DEFINITION IRREDUCIBLE-PP))
     (82 31
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (78 3 (:DEFINITION REDUCIBLE-PP))
     (70 70 (:REWRITE EQUIVALENCE-LAW))
     (70 10
         (:REWRITE DIVIDES-PP-IMPLIES-WITNESS=QQ_E))
     (56 44 (:REWRITE DIVIDES-P-SUFF))
     (44 44
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (40 10 (:REWRITE DIVIDES-PP-SUFF))
     (21 21 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
     (20 20 (:REWRITE CLOSURE-LAWS))
     (18 3
         (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
     (14 10 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (12 10 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (12 6 (:DEFINITION MV-NTH))
     (9 6 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
     (8 8 (:TYPE-PRESCRIPTION IRREDUCIBLE-PP))
     (6 6 (:TYPE-PRESCRIPTION NATP-SIZE))
     (3 3 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
     (3 3 (:REWRITE REDUCIBLE-PP-SUFF))
     (3 3 (:REWRITE DEFAULT-CDR))
     (3 3 (:REWRITE DEFAULT-CAR)))
(TRANSITIVITY-UNIT-ASSOCIATES-PP
     (874 259 (:REWRITE UNIT-P-IMPLIES-EDP))
     (506 146
          (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
     (502 54 (:DEFINITION UNIT-P))
     (351 9 (:DEFINITION IRREDUCIBLE-PP))
     (346 54 (:DEFINITION DIVIDES-P))
     (259 259 (:TYPE-PRESCRIPTION UNIT-P))
     (225 9 (:DEFINITION REDUCIBLE-PP))
     (143 71
          (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (102 54 (:REWRITE DIVIDES-P-SUFF))
     (92 92 (:REWRITE EQUIVALENCE-LAW))
     (58 58 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
     (54 54
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (54 9
         (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
     (48 48 (:REWRITE CLOSURE-LAWS))
     (36 18 (:DEFINITION MV-NTH))
     (27 18 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
     (18 18 (:TYPE-PRESCRIPTION NATP-SIZE))
     (9 9 (:TYPE-PRESCRIPTION IRREDUCIBLE-PP))
     (9 9 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
     (9 9 (:REWRITE REDUCIBLE-PP-SUFF))
     (9 9 (:REWRITE DEFAULT-CDR))
     (9 9 (:REWRITE DEFAULT-CAR))
     (1 1
        (:REWRITE CLOSURE-LAWS-FOR-++_E-&-**_E)))
(UNIT-ASSOCIATES-PP-IS-AN-EQUIVALENCE
     (6 6 (:REWRITE UNIT-ASSOCIATES-PP-SUFF)))
(ASSOCIATES-PP-IMPLIES-IFF-EDP
     (5572 1344 (:REWRITE UNIT-P-IMPLIES-EDP))
     (5501 1244 (:REWRITE EQUIVALENCE-LAW))
     (5490 74 (:DEFINITION UNIT-P))
     (4427 28 (:DEFINITION DIVIDES-P))
     (3857 18 (:REWRITE ZERO-DIVISOR-LAW))
     (2407 2397 (:REWRITE CLOSURE-LAWS))
     (1252 74 (:REWRITE DIVIDES-P-SUFF))
     (230 230 (:TYPE-PRESCRIPTION UNIT-P))
     (164 74
          (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (92 92
         (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
     (31 2 (:REWRITE DIVIDES-PP-SUFF))
     (22 22 (:EQUIVALENCE ==_E-EQUIVALENCE-LAW))
     (6 2 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (6 2 (:REWRITE PROJECTION-LAWS))
     (2 2 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (2 2 (:REWRITE RIGHT-UNICITY-LAWS))
     (2 2 (:REWRITE NULLITY-LAWS))
     (1 1 (:REWRITE RIGHT-UNICITY-LAW-FOR-*_E))
     (1 1 (:REWRITE GCD-PP-ASSOCIATES-PP))
     (1 1
        (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E)))
(ASSOCIATES-PP-REFINES-UNIT-ASSOCIATES-PP-LEMMA-1
     (254 68 (:REWRITE UNIT-P-IMPLIES-EDP))
     (169 17 (:DEFINITION UNIT-P))
     (121 17 (:DEFINITION DIVIDES-P))
     (68 68 (:TYPE-PRESCRIPTION UNIT-P))
     (66 4 (:REWRITE DIVIDES-PP-SUFF))
     (37 12
         (:REWRITE INVERSE-CANCELLATION-LAWS-**_E))
     (34 34 (:REWRITE EQUIVALENCE-LAW))
     (31 17 (:REWRITE DIVIDES-P-SUFF))
     (28 8 (:REWRITE PROJECTION-LAWS))
     (22 22 (:REWRITE CLOSURE-LAWS))
     (20 4 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (17 17
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (13 7
         (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
     (6 2 (:REWRITE ZERO-DIVISOR-LAW-FOR-**_E))
     (4 4 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (4 4 (:REWRITE RIGHT-UNICITY-LAWS))
     (4 4 (:REWRITE NULLITY-LAWS))
     (4 2
        (:REWRITE DIVIDES-PP-IMPLIES-RR_E=0-LEMMA-1))
     (4 2 (:REWRITE DIVIDES-P-IMPLIES-RR_E=0))
     (3 1
        (:REWRITE ASSOCIATIVITY-LAWS-FOR-++_E-&-**_E))
     (2 2 (:TYPE-PRESCRIPTION DIVIDES-PP))
     (2 2 (:REWRITE GCD-PP-ASSOCIATES-PP)))
(ASSOCIATES-PP-REFINES-UNIT-ASSOCIATES-PP-LEMMA-2
     (790 130 (:REWRITE UNIT-P-IMPLIES-EDP))
     (657 18 (:DEFINITION UNIT-P))
     (540 18 (:DEFINITION DIVIDES-P))
     (480 250 (:REWRITE EQUIVALENCE-LAW))
     (180 21 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (159 18
          (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
     (130 130 (:TYPE-PRESCRIPTION UNIT-P))
     (99 18 (:REWRITE DIVIDES-P-SUFF))
     (99 11 (:REWRITE ZERO-DIVISOR-LAW))
     (72 8 (:REWRITE DIVIDES-P-IMPLIES-RR_E=0))
     (64 10
         (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
     (63 18
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (42 2 (:REWRITE UNIT-PP-**_E-INVERSE))
     (25 8
         (:REWRITE DIVIDES-PP-IMPLIES-RR_E=0-LEMMA-1))
     (21 21 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (10 7 (:REWRITE NULLITY-LAWS))
     (6 1
        (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (2 2
        (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
     (2 2 (:REWRITE GCD-PP-ASSOCIATES-PP)))
(ASSOCIATES-PP-REFINES-UNIT-ASSOCIATES-PP-LEMMA-3
     (1742 251 (:REWRITE UNIT-P-IMPLIES-EDP))
     (1506 42 (:DEFINITION UNIT-P))
     (1215 42 (:DEFINITION DIVIDES-P))
     (1164 634 (:REWRITE EQUIVALENCE-LAW))
     (364 364 (:REWRITE CLOSURE-LAWS))
     (251 251 (:TYPE-PRESCRIPTION UNIT-P))
     (248 42 (:REWRITE DIVIDES-P-SUFF))
     (234 26 (:REWRITE ZERO-DIVISOR-LAW))
     (207 21
          (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
     (182 15 (:REWRITE DIVIDES-PP-SUFF))
     (138 42
          (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (121 18
          (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
     (88 15 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (84 1 (:DEFINITION IRREDUCIBLE-PP))
     (78 9
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (53 11 (:REWRITE PROJECTION-LAWS))
     (44 4 (:REWRITE DIVIDES-P-IMPLIES-RR_E=0))
     (44 1 (:DEFINITION REDUCIBLE-PP))
     (41 41 (:TYPE-PRESCRIPTION DIVIDES-PP))
     (26 1
         (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
     (16 11 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
     (15 15 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (13 1 (:REWRITE REDUCIBLE-PP-SUFF))
     (10 10 (:TYPE-PRESCRIPTION NATP-SIZE))
     (10 4
         (:REWRITE DIVIDES-PP-IMPLIES-RR_E=0-LEMMA-1))
     (8 8 (:REWRITE RIGHT-UNICITY-LAWS))
     (8 8 (:REWRITE NULLITY-LAWS))
     (4 4 (:TYPE-PRESCRIPTION IRREDUCIBLE-PP))
     (4 2 (:DEFINITION MV-NTH))
     (2 2
        (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
     (2 2 (:REWRITE GCD-PP-ASSOCIATES-PP))
     (2 1 (:LINEAR SIZE->=-SIZE-1_E))
     (1 1 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
     (1 1 (:REWRITE DEFAULT-CDR))
     (1 1 (:REWRITE DEFAULT-CAR)))
(ASSOCIATES-PP-REFINES-UNIT-ASSOCIATES-PP
     (602 124 (:REWRITE UNIT-P-IMPLIES-EDP))
     (479 19 (:DEFINITION UNIT-P))
     (369 19 (:DEFINITION DIVIDES-P))
     (295 146 (:REWRITE EQUIVALENCE-LAW))
     (124 124 (:TYPE-PRESCRIPTION UNIT-P))
     (100 6 (:REWRITE DIVIDES-PP-SUFF))
     (91 19 (:REWRITE DIVIDES-P-SUFF))
     (74 8
         (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
     (69 19
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (55 7 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (45 5 (:REWRITE ZERO-DIVISOR-LAW))
     (16 16 (:TYPE-PRESCRIPTION DIVIDES-PP))
     (7 7 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (5 5 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
     (3 3 (:REWRITE GCD-PP-ASSOCIATES-PP))
     (2 2 (:REWRITE RIGHT-UNICITY-LAWS)))
(UNIT-ASSOCIATES-PP-IMPLIES-IFF-EDP
     (270 52 (:REWRITE UNIT-P-IMPLIES-EDP))
     (227 11 (:DEFINITION UNIT-P))
     (191 11 (:DEFINITION DIVIDES-P))
     (152 74 (:REWRITE EQUIVALENCE-LAW))
     (52 52 (:TYPE-PRESCRIPTION UNIT-P))
     (44 44 (:REWRITE CLOSURE-LAWS))
     (36 4 (:REWRITE ZERO-DIVISOR-LAW))
     (25 11 (:REWRITE DIVIDES-P-SUFF))
     (21 11
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (13 1
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (13 1 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (13 1 (:REWRITE DIVIDES-PP-SUFF))
     (13 1
         (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
     (2 2
        (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
     (1 1 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
     (1 1 (:REWRITE TRANSITIVITY-DIVIDES-PP)))
(UNIT-ASSOCIATES-PP-REFINES-ASSOCIATES-PP-LEMMA-1
     (325 60 (:REWRITE UNIT-P-IMPLIES-EDP))
     (278 11 (:DEFINITION UNIT-P))
     (237 11 (:DEFINITION DIVIDES-P))
     (195 98 (:REWRITE EQUIVALENCE-LAW))
     (104 10
          (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
     (73 1 (:DEFINITION IRREDUCIBLE-PP))
     (60 60 (:TYPE-PRESCRIPTION UNIT-P))
     (45 5 (:REWRITE ZERO-DIVISOR-LAW))
     (44 1 (:DEFINITION REDUCIBLE-PP))
     (35 5
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (29 11 (:REWRITE DIVIDES-P-SUFF))
     (26 1
         (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
     (23 11
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (14 9 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
     (9 9 (:TYPE-PRESCRIPTION NATP-SIZE))
     (9 3 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (4 2 (:DEFINITION MV-NTH))
     (3 3 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (3 1 (:REWRITE REDUCIBLE-PP-SUFF))
     (2 2
        (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
     (2 1 (:LINEAR SIZE->=-SIZE-1_E))
     (1 1 (:TYPE-PRESCRIPTION IRREDUCIBLE-PP))
     (1 1 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
     (1 1 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
     (1 1 (:REWRITE NULLITY-LAWS))
     (1 1 (:REWRITE DEFAULT-CDR))
     (1 1 (:REWRITE DEFAULT-CAR)))
(UNIT-ASSOCIATES-PP-REFINES-ASSOCIATES-PP
     (234 39 (:REWRITE UNIT-P-IMPLIES-EDP))
     (201 7 (:DEFINITION UNIT-P))
     (165 7 (:DEFINITION DIVIDES-P))
     (154 74 (:REWRITE EQUIVALENCE-LAW))
     (50 50 (:REWRITE CLOSURE-LAWS))
     (39 39 (:TYPE-PRESCRIPTION UNIT-P))
     (36 4 (:REWRITE ZERO-DIVISOR-LAW))
     (29 7 (:REWRITE DIVIDES-P-SUFF))
     (19 7
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (2 2 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
     (2 2 (:REWRITE GCD-PP-ASSOCIATES-PP)))
(UNIT-ASSOCIATES-PP-IMPLIES-REDUCIBLE-PP-LEMMA-1
     (735 132 (:REWRITE UNIT-P-IMPLIES-EDP))
     (622 19 (:DEFINITION UNIT-P))
     (507 19 (:DEFINITION DIVIDES-P))
     (471 238 (:REWRITE EQUIVALENCE-LAW))
     (135 42
          (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
     (134 134 (:REWRITE CLOSURE-LAWS))
     (132 132 (:TYPE-PRESCRIPTION UNIT-P))
     (99 11 (:REWRITE ZERO-DIVISOR-LAW))
     (93 19 (:REWRITE DIVIDES-P-SUFF))
     (73 21
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (64 8 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
     (64 3 (:DEFINITION IRREDUCIBLE-PP))
     (63 19
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (30 3
         (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
     (14 9 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
     (10 2 (:REWRITE ZERO-DIVISOR-LAW-FOR-**_E))
     (9 9 (:TYPE-PRESCRIPTION NATP-SIZE))
     (9 9 (:REWRITE DEFAULT-CDR))
     (9 9 (:REWRITE DEFAULT-CAR))
     (6 6
        (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
     (4 4 (:TYPE-PRESCRIPTION IRREDUCIBLE-PP))
     (2 2 (:REWRITE UNIT-PP-CLOSURE-**_E))
     (2 1 (:LINEAR SIZE->=-SIZE-1_E))
     (1 1 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
     (1 1
        (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E)))
(UNIT-ASSOCIATES-PP-IMPLIES-REDUCIBLE-PP-LEMMA-2
     (1020 205 (:REWRITE UNIT-P-IMPLIES-EDP))
     (841 41 (:DEFINITION UNIT-P))
     (699 41 (:DEFINITION DIVIDES-P))
     (534 284 (:REWRITE EQUIVALENCE-LAW))
     (205 205 (:TYPE-PRESCRIPTION UNIT-P))
     (156 12
          (:REWRITE INVERSE-CANCELLATION-LAWS-**_E))
     (138 138 (:REWRITE CLOSURE-LAWS))
     (126 19
          (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (108 12 (:REWRITE ZERO-DIVISOR-LAW))
     (99 41 (:REWRITE DIVIDES-P-SUFF))
     (79 41
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (78 38
         (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
     (74 6
         (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
     (47 5 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
     (36 2 (:DEFINITION IRREDUCIBLE-PP))
     (26 2 (:REWRITE COMMUTATIVITY-2-LAWS))
     (12 5 (:REWRITE UNIT-PP-CLOSURE-**_E))
     (10 2 (:REWRITE ZERO-DIVISOR-LAW-FOR-**_E))
     (7 7 (:REWRITE DEFAULT-CAR))
     (6 6 (:REWRITE DEFAULT-CDR))
     (5 5
        (:REWRITE UNIT-ASSOCIATES-PP-IMPLIES-REDUCIBLE-PP-LEMMA-1))
     (4 4
        (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
     (4 2
        (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
     (2 2 (:TYPE-PRESCRIPTION IRREDUCIBLE-PP))
     (2 2 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
     (2 2 (:REWRITE PROJECTION-LAWS)))
(UNIT-ASSOCIATES-PP-IMPLIES-REDUCIBLE-PP-LEMMA-3
     (1806 392 (:REWRITE UNIT-P-IMPLIES-EDP))
     (1417 85 (:DEFINITION UNIT-P))
     (1162 85 (:DEFINITION DIVIDES-P))
     (778 450 (:REWRITE EQUIVALENCE-LAW))
     (592 80
          (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
     (396 17 (:DEFINITION IRREDUCIBLE-PP))
     (392 392 (:TYPE-PRESCRIPTION UNIT-P))
     (353 36
          (:REWRITE INVERSE-CANCELLATION-LAWS-**_E))
     (201 40
          (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (190 190 (:REWRITE CLOSURE-LAWS))
     (169 85 (:REWRITE DIVIDES-P-SUFF))
     (144 16 (:REWRITE ZERO-DIVISOR-LAW))
     (136 8 (:REWRITE CANCELLATION-LAWS-FOR-**_E))
     (133 85
          (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (127 17
          (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
     (83 19 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
     (56 36 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
     (56 8 (:REWRITE UNIT-PP-CLOSURE-**_E))
     (36 36 (:TYPE-PRESCRIPTION NATP-SIZE))
     (19 19
         (:REWRITE UNIT-ASSOCIATES-PP-IMPLIES-REDUCIBLE-PP-LEMMA-2))
     (19 19
         (:REWRITE UNIT-ASSOCIATES-PP-IMPLIES-REDUCIBLE-PP-LEMMA-1))
     (18 18 (:TYPE-PRESCRIPTION IRREDUCIBLE-PP))
     (13 13 (:REWRITE DEFAULT-CAR))
     (12 12 (:REWRITE DEFAULT-CDR))
     (10 2 (:REWRITE ZERO-DIVISOR-LAW-FOR-**_E))
     (8 4 (:LINEAR SIZE->=-SIZE-1_E))
     (2 2
        (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
     (2 2 (:REWRITE UNIT-ASSOCIATES-PP-SUFF)))
(UNIT-ASSOCIATES-PP-IMPLIES-REDUCIBLE-PP-LEMMA-4
     (1762 380 (:REWRITE UNIT-P-IMPLIES-EDP))
     (1385 81 (:DEFINITION UNIT-P))
     (1132 81 (:DEFINITION DIVIDES-P))
     (774 446 (:REWRITE EQUIVALENCE-LAW))
     (678 98
          (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
     (439 18 (:DEFINITION IRREDUCIBLE-PP))
     (380 380 (:TYPE-PRESCRIPTION UNIT-P))
     (312 24
          (:REWRITE INVERSE-CANCELLATION-LAWS-**_E))
     (297 49
          (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (192 192 (:REWRITE CLOSURE-LAWS))
     (171 81 (:REWRITE DIVIDES-P-SUFF))
     (153 18
          (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
     (144 16 (:REWRITE ZERO-DIVISOR-LAW))
     (129 81
          (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (84 20 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
     (84 13 (:REWRITE UNIT-PP-CLOSURE-**_E))
     (70 45 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
     (68 4 (:REWRITE CANCELLATION-LAWS-FOR-**_E))
     (45 45 (:TYPE-PRESCRIPTION NATP-SIZE))
     (20 20
         (:REWRITE UNIT-ASSOCIATES-PP-IMPLIES-REDUCIBLE-PP-LEMMA-3))
     (20 20
         (:REWRITE UNIT-ASSOCIATES-PP-IMPLIES-REDUCIBLE-PP-LEMMA-2))
     (20 20
         (:REWRITE UNIT-ASSOCIATES-PP-IMPLIES-REDUCIBLE-PP-LEMMA-1))
     (19 19 (:TYPE-PRESCRIPTION IRREDUCIBLE-PP))
     (16 4 (:REWRITE ZERO-DIVISOR-LAW-FOR-**_E))
     (13 13 (:REWRITE DEFAULT-CAR))
     (10 10 (:REWRITE DEFAULT-CDR))
     (10 5 (:LINEAR SIZE->=-SIZE-1_E))
     (2 2
        (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
     (2 2 (:REWRITE UNIT-ASSOCIATES-PP-SUFF)))
(UNIT-ASSOCIATES-PP-IMPLIES-REDUCIBLE-PP-LEMMA-5
     (1918 405 (:REWRITE UNIT-P-IMPLIES-EDP))
     (1530 83 (:DEFINITION UNIT-P))
     (1234 83 (:DEFINITION DIVIDES-P))
     (888 504 (:REWRITE EQUIVALENCE-LAW))
     (618 80
          (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
     (422 17 (:DEFINITION IRREDUCIBLE-PP))
     (405 405 (:TYPE-PRESCRIPTION UNIT-P))
     (312 24
          (:REWRITE INVERSE-CANCELLATION-LAWS-**_E))
     (220 220 (:REWRITE CLOSURE-LAWS))
     (212 83 (:REWRITE DIVIDES-P-SUFF))
     (201 40
          (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (162 18 (:REWRITE ZERO-DIVISOR-LAW))
     (150 83
          (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (127 17
          (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
     (83 19 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
     (68 4 (:REWRITE CANCELLATION-LAWS-FOR-**_E))
     (60 8 (:REWRITE UNIT-PP-CLOSURE-**_E))
     (56 36 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
     (36 36 (:TYPE-PRESCRIPTION NATP-SIZE))
     (19 19
         (:REWRITE UNIT-ASSOCIATES-PP-IMPLIES-REDUCIBLE-PP-LEMMA-4))
     (19 19
         (:REWRITE UNIT-ASSOCIATES-PP-IMPLIES-REDUCIBLE-PP-LEMMA-3))
     (19 19
         (:REWRITE UNIT-ASSOCIATES-PP-IMPLIES-REDUCIBLE-PP-LEMMA-2))
     (19 19
         (:REWRITE UNIT-ASSOCIATES-PP-IMPLIES-REDUCIBLE-PP-LEMMA-1))
     (18 18 (:TYPE-PRESCRIPTION IRREDUCIBLE-PP))
     (13 13 (:REWRITE DEFAULT-CAR))
     (10 10 (:REWRITE DEFAULT-CDR))
     (10 2 (:REWRITE ZERO-DIVISOR-LAW-FOR-**_E))
     (8 4 (:LINEAR SIZE->=-SIZE-1_E))
     (2 2
        (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
     (2 2 (:REWRITE UNIT-ASSOCIATES-PP-SUFF)))
(UNIT-ASSOCIATES-PP-IMPLIES-REDUCIBLE-PP
     (8942 1840 (:REWRITE UNIT-P-IMPLIES-EDP))
     (7535 284 (:DEFINITION UNIT-P))
     (6664 284 (:DEFINITION DIVIDES-P))
     (5311 2442 (:REWRITE EQUIVALENCE-LAW))
     (1840 1840 (:TYPE-PRESCRIPTION UNIT-P))
     (1510 1510 (:REWRITE CLOSURE-LAWS))
     (1359 151 (:REWRITE ZERO-DIVISOR-LAW))
     (1267 522
           (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
     (1187 261
           (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (777 22 (:DEFINITION IRREDUCIBLE-PP))
     (750 99 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
     (587 284
          (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (587 284 (:REWRITE DIVIDES-P-SUFF))
     (465 96
          (:REWRITE INVERSE-CANCELLATION-LAWS-**_E))
     (247 33 (:REWRITE UNIT-PP-CLOSURE-**_E))
     (76 76 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
     (58 22
         (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
     (54 18 (:REWRITE ZERO-DIVISOR-LAW-FOR-**_E))
     (29 29 (:TYPE-PRESCRIPTION IRREDUCIBLE-PP))
     (13 1
         (:REWRITE ASSOCIATIVITY-LAWS-FOR-++_E-&-**_E)))
(UNIT-ASSOCIATES-PP-IMPLIES-EQUAL-REDUCIBLE-PP
     (38 2 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
     (24 2 (:DEFINITION UNIT-PP))
     (16 8 (:REWRITE UNIT-P-IMPLIES-EDP))
     (8 8 (:TYPE-PRESCRIPTION UNIT-P))
     (6 2
        (:REWRITE UNIT-ASSOCIATES-PP-REFINES-ASSOCIATES-PP-LEMMA-1))
     (6 2
        (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (6 2 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (6 2 (:REWRITE DIVIDES-PP-SUFF))
     (4 4
        (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
     (2 2 (:TYPE-PRESCRIPTION UNIT-PP))
     (2 2 (:TYPE-PRESCRIPTION DIVIDES-PP))
     (2 2 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (2 2 (:REWRITE REDUCIBLE-PP-SUFF))
     (1 1 (:REWRITE UNIT-ASSOCIATES-PP-SUFF)))
(UNIT-ASSOCIATES-PP-IMPLIES-EQUAL-IRREDUCIBLE-PP
     (118 24 (:REWRITE UNIT-P-IMPLIES-EDP))
     (102 4 (:DEFINITION UNIT-P))
     (90 4 (:DEFINITION DIVIDES-P))
     (70 32 (:REWRITE EQUIVALENCE-LAW))
     (56 2 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
     (44 4 (:REWRITE DIVIDES-PP-SUFF))
     (40 40 (:EQUIVALENCE ==_E-EQUIVALENCE-LAW))
     (28 28 (:REWRITE CLOSURE-LAWS))
     (26 2
         (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
     (24 24 (:TYPE-PRESCRIPTION UNIT-P))
     (18 2 (:REWRITE ZERO-DIVISOR-LAW))
     (16 4
         (:REWRITE UNIT-ASSOCIATES-PP-REFINES-ASSOCIATES-PP-LEMMA-1))
     (12 4
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (12 4 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (8 8
        (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
     (8 4
        (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (8 4 (:REWRITE DIVIDES-P-SUFF))
     (5 5 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
     (4 4 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (4 4 (:REWRITE RIGHT-UNICITY-LAWS))
     (4 4 (:REWRITE NULLITY-LAWS))
     (2 2 (:TYPE-PRESCRIPTION UNIT-PP))
     (2 2 (:REWRITE REDUCIBLE-PP-SUFF)))
(MEMBER-UNIT-ASSOCIATE)
(MEMBER-UNIT-ASSOCIATE-PP)
(MEMBER-UNIT-ASSOCIATE-=-MEMBER-UNIT-ASSOCIATE-PP
     (14 14 (:REWRITE DEFAULT-CAR))
     (8 8 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
     (5 5 (:REWRITE UNIT-ASSOCIATES-P-SUFF))
     (4 4 (:REWRITE DEFAULT-CDR)))
(DELETE-ONE-UNIT-ASSOCIATE)
(DELETE-ONE-UNIT-ASSOCIATE-PP)
(DELETE-ONE-UNIT-ASSOCIATE-=-DELETE-ONE-UNIT-ASSOCIATE-PP
     (20 20 (:REWRITE DEFAULT-CAR))
     (10 10 (:REWRITE DEFAULT-CDR))
     (8 8 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
     (5 5 (:REWRITE UNIT-ASSOCIATES-P-SUFF)))
(BAG-EQUAL-UNIT-ASSOCIATES)
(BAG-EQUAL-UNIT-ASSOCIATES-PP)
(BAG-EQUAL-UNIT-ASSOCIATES-=-BAG-EQUAL-UNIT-ASSOCIATES-PP
     (57 57 (:REWRITE DEFAULT-CAR))
     (40 40 (:REWRITE DEFAULT-CDR))
     (28 4
         (:DEFINITION DELETE-ONE-UNIT-ASSOCIATE))
     (12 12 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
     (12 12 (:REWRITE UNIT-ASSOCIATES-P-SUFF)))
(LEN-DELETE-ONE-UNIT-ASSOCIATE (28 15 (:REWRITE DEFAULT-+-2))
                               (15 15 (:REWRITE DEFAULT-CAR))
                               (15 15 (:REWRITE DEFAULT-+-1))
                               (14 14 (:REWRITE DEFAULT-CDR))
                               (12 12 (:REWRITE UNIT-ASSOCIATES-P-SUFF))
                               (3 3 (:REWRITE EQUAL-CONSTANT-+)))
(LEN-DELETE-ONE-UNIT-ASSOCIATE-PP (28 15 (:REWRITE DEFAULT-+-2))
                                  (15 15 (:REWRITE DEFAULT-CAR))
                                  (15 15 (:REWRITE DEFAULT-+-1))
                                  (14 14 (:REWRITE DEFAULT-CDR))
                                  (12 12 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
                                  (3 3 (:REWRITE EQUAL-CONSTANT-+)))
(BAG-EQUAL-UNIT-ASSOCIATES->EQUAL-LEN
     (126 18
          (:DEFINITION DELETE-ONE-UNIT-ASSOCIATE))
     (92 92 (:REWRITE DEFAULT-CDR))
     (81 81 (:REWRITE DEFAULT-CAR))
     (60 30 (:REWRITE DEFAULT-+-2))
     (36 36 (:REWRITE UNIT-ASSOCIATES-P-SUFF))
     (30 30 (:REWRITE DEFAULT-+-1))
     (5 5 (:REWRITE EQUAL-CONSTANT-+)))
(BAG-EQUAL-UNIT-ASSOCIATES-PP->EQUAL-LEN
     (108 18
          (:DEFINITION DELETE-ONE-UNIT-ASSOCIATE-PP))
     (92 92 (:REWRITE DEFAULT-CDR))
     (81 81 (:REWRITE DEFAULT-CAR))
     (60 30 (:REWRITE DEFAULT-+-2))
     (36 36 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
     (30 30 (:REWRITE DEFAULT-+-1))
     (5 5 (:REWRITE EQUAL-CONSTANT-+)))
(MEMBER-UNIT-ASSOCIATE-PP-DELETE-ONE-UNIT-ASSOCIATE-PP
     (60 60 (:REWRITE DEFAULT-CAR))
     (57 57 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
     (46 46 (:REWRITE DEFAULT-CDR)))
(UNIT-ASSOCIATES-PP-MEMBER-UNIT-ASSOCIATE-PP
     (18 18 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
     (12 12 (:REWRITE DEFAULT-CAR))
     (4 4 (:REWRITE DEFAULT-CDR)))
(UNIT-ASSOCIATES-PP-IMPLIES-IFF-MEMBER-UNIT-ASSOCIATE-PP
     (29 3
         (:DEFINITION MEMBER-UNIT-ASSOCIATE-PP))
     (5 5 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
     (3 3 (:REWRITE DEFAULT-CDR))
     (3 3 (:REWRITE DEFAULT-CAR)))
(BAG-EQUAL-UNIT-ASSOCIATES-PP->IFF-MEMBER-UNIT-ASSOCIATE-PP
     (63 63 (:REWRITE DEFAULT-CAR))
     (45 45 (:REWRITE DEFAULT-CDR))
     (42 7
         (:DEFINITION DELETE-ONE-UNIT-ASSOCIATE-PP))
     (37 37 (:REWRITE UNIT-ASSOCIATES-PP-SUFF)))
(BAG-EQUAL-UNIT-ASSOCIATES->IFF-MEMBER-UNIT-ASSOCIATE
     (8 8 (:REWRITE DEFAULT-CAR))
     (7 7 (:REWRITE DEFAULT-CDR))
     (6 1
        (:DEFINITION DELETE-ONE-UNIT-ASSOCIATE-PP))
     (5 5 (:REWRITE UNIT-ASSOCIATES-PP-SUFF)))
(MULTIPLICITY-UNIT-ASSOCIATE)
(MULTIPLICITY-UNIT-ASSOCIATE-PP)
(MULTIPLICITY-UNIT-ASSOCIATE-=-MULTIPLICITY-UNIT-ASSOCIATE-PP
     (14 14 (:REWRITE DEFAULT-CAR))
     (12 6 (:REWRITE DEFAULT-+-2))
     (8 8 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
     (8 8 (:REWRITE DEFAULT-CDR))
     (6 6 (:REWRITE DEFAULT-+-1))
     (5 5 (:REWRITE UNIT-ASSOCIATES-P-SUFF)))
(MULTIPLICITY-UNIT-ASSOCIATE-PP-DELETE-ONE-UNIT-ASSOCIATE-PP-1
     (40 21 (:REWRITE DEFAULT-+-2))
     (38 38 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
     (36 36 (:REWRITE DEFAULT-CAR))
     (34 34 (:REWRITE DEFAULT-CDR))
     (21 21 (:REWRITE DEFAULT-+-1))
     (5 5 (:REWRITE EQUAL-CONSTANT-+)))
(MULTIPLICITY-UNIT-ASSOCIATE-PP-DELETE-ONE-UNIT-ASSOCIATE-PP-2
     (38 38 (:REWRITE DEFAULT-CDR))
     (32 32 (:REWRITE DEFAULT-CAR))
     (31 31 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
     (26 13 (:REWRITE DEFAULT-+-2))
     (13 13 (:REWRITE DEFAULT-+-1)))
(BAG-EQUAL-UNIT-ASSOCIATES-PP->EQUAL-MULTIPLICITY-UNIT-ASSOCIATE-PP
     (123 123 (:REWRITE DEFAULT-CDR))
     (114 114 (:REWRITE DEFAULT-CAR))
     (114 19
          (:DEFINITION DELETE-ONE-UNIT-ASSOCIATE-PP))
     (79 79 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
     (66 33 (:REWRITE DEFAULT-+-2))
     (64 16
         (:DEFINITION MEMBER-UNIT-ASSOCIATE-PP))
     (33 33 (:REWRITE DEFAULT-+-1))
     (20 5
         (:REWRITE MEMBER-UNIT-ASSOCIATE-PP-DELETE-ONE-UNIT-ASSOCIATE-PP))
     (5 5 (:REWRITE EQUAL-CONSTANT-+)))
(BAG-EQUAL-UNIT-ASSOCIATES->EQUAL-MULTIPLICITY-UNIT-ASSOCIATE)
(DIVIDES-PP-MEMBER-UNIT-ASSOCIATE-PP-**_E-LST
     (685 123 (:REWRITE UNIT-P-IMPLIES-EDP))
     (598 19 (:DEFINITION UNIT-P))
     (514 19 (:DEFINITION DIVIDES-P))
     (452 218 (:REWRITE EQUIVALENCE-LAW))
     (123 123 (:TYPE-PRESCRIPTION UNIT-P))
     (108 12 (:REWRITE ZERO-DIVISOR-LAW))
     (65 19 (:REWRITE DIVIDES-P-SUFF))
     (51 7 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (49 19
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (27 27 (:REWRITE DEFAULT-CAR))
     (8 8 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
     (6 6 (:REWRITE DEFAULT-CDR))
     (5 5 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (1 1 (:REWRITE NULLITY-LAWS)))
(DIVISORS-OF-IRREDUCIBLE-PP
     (602 99 (:REWRITE UNIT-P-IMPLIES-EDP))
     (513 19 (:DEFINITION UNIT-P))
     (423 19 (:DEFINITION DIVIDES-P))
     (346 186 (:REWRITE EQUIVALENCE-LAW))
     (104 104 (:REWRITE CLOSURE-LAWS))
     (99 99 (:TYPE-PRESCRIPTION UNIT-P))
     (80 20
         (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
     (72 8 (:REWRITE ZERO-DIVISOR-LAW))
     (71 19 (:REWRITE DIVIDES-P-SUFF))
     (61 7 (:REWRITE DIVIDES-PP-SUFF))
     (52 10
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (47 19
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (39 7 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (31 7
         (:REWRITE UNIT-ASSOCIATES-PP-REFINES-ASSOCIATES-PP-LEMMA-1))
     (16 3
         (:REWRITE DIVIDES-PP-IMPLIES-WITNESS=QQ_E))
     (8 3
        (:REWRITE ASSOCIATES-PP-REFINES-UNIT-ASSOCIATES-PP-LEMMA-2))
     (7 7 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (6 2
        (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
     (5 5 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
     (2 2 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
     (2 2 (:REWRITE RIGHT-UNICITY-LAWS))
     (2 2 (:REWRITE NULLITY-LAWS)))
(GCD-PP-OF-IRREDUCIBLE-PP
     (61 2
         (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
     (45 3 (:REWRITE DIVIDES-PP-SUFF))
     (38 10 (:REWRITE UNIT-P-IMPLIES-EDP))
     (30 25 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
     (27 3 (:DEFINITION UNIT-P))
     (21 4 (:LINEAR SIZE->=-SIZE-1_E))
     (21 3 (:DEFINITION DIVIDES-P))
     (19 3 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (18 18 (:TYPE-PRESCRIPTION NATP-SIZE))
     (18 3
         (:REWRITE UNIT-ASSOCIATES-PP-REFINES-ASSOCIATES-PP-LEMMA-1))
     (10 10 (:TYPE-PRESCRIPTION UNIT-P))
     (6 6 (:REWRITE EQUIVALENCE-LAW))
     (5 5 (:REWRITE CLOSURE-LAWS))
     (3 3 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (3 3
        (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (3 3 (:REWRITE DIVIDES-P-SUFF))
     (3 1 (:REWRITE PROJECTION-LAWS))
     (2 2 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
     (2 2 (:REWRITE RIGHT-UNICITY-LAWS))
     (2 2 (:REWRITE NULLITY-LAWS))
     (1 1 (:REWRITE GCD-PP-NECC))
     (1 1 (:REWRITE |1_E-0_E|)))
(GCD-PP-OF-IRREDUCIBLE-PP-DIVIDES-PP
     (1130 304 (:REWRITE UNIT-P-IMPLIES-EDP))
     (783 87 (:DEFINITION UNIT-P))
     (609 87 (:DEFINITION DIVIDES-P))
     (478 51
          (:REWRITE UNIT-ASSOCIATES-PP-REFINES-ASSOCIATES-PP-LEMMA-1))
     (477 51 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (427 42 (:REWRITE DIVIDES-PP-SUFF))
     (304 304 (:TYPE-PRESCRIPTION UNIT-P))
     (196 7
          (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
     (174 174 (:REWRITE EQUIVALENCE-LAW))
     (100 70 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
     (87 87
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (87 87 (:REWRITE DIVIDES-P-SUFF))
     (63 63 (:TYPE-PRESCRIPTION NATP-SIZE))
     (36 9 (:LINEAR SIZE->=-SIZE-1_E))
     (12 4 (:REWRITE PROJECTION-LAWS))
     (11 11 (:REWRITE CLOSURE-LAWS))
     (7 7 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
     (7 7 (:REWRITE GCD-PP-NECC))
     (5 5 (:REWRITE RIGHT-UNICITY-LAWS))
     (5 5 (:REWRITE NULLITY-LAWS))
     (3 3
        (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
     (2 1
        (:REWRITE DIVIDES-PP-IMPLIES-RR_E=0-LEMMA-1))
     (2 1 (:REWRITE DIVIDES-P-IMPLIES-RR_E=0))
     (1 1 (:REWRITE |1_E-0_E|)))
(UNIT-PP-BEZOUT)
(ASSOCIATE-PP-UNIT-PP
     (190 28 (:REWRITE UNIT-P-IMPLIES-EDP))
     (158 8 (:DEFINITION UNIT-P))
     (118 8 (:DEFINITION DIVIDES-P))
     (106 72 (:REWRITE EQUIVALENCE-LAW))
     (42 6
         (:REWRITE UNIT-ASSOCIATES-PP-REFINES-ASSOCIATES-PP-LEMMA-1))
     (40 6 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (32 8 (:REWRITE DIVIDES-P-SUFF))
     (28 28 (:TYPE-PRESCRIPTION UNIT-P))
     (28 28 (:REWRITE CLOSURE-LAWS))
     (26 2 (:REWRITE DIVIDES-PP-SUFF))
     (18 2 (:REWRITE ZERO-DIVISOR-LAW))
     (16 8
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (8 8
        (:TYPE-PRESCRIPTION UNIT-ASSOCIATES-PP))
     (8 8 (:EQUIVALENCE ==_E-EQUIVALENCE-LAW))
     (4 4 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
     (2 2 (:REWRITE |1_E-0_E|))
     (1 1 (:REWRITE GCD-PP-ASSOCIATES-PP)))
(IRREDUCIBLE-PP-GCD=1_E
     (5406 976 (:REWRITE UNIT-P-IMPLIES-EDP))
     (4753 123 (:DEFINITION UNIT-P))
     (4210 123 (:DEFINITION DIVIDES-P))
     (3713 1814 (:REWRITE EQUIVALENCE-LAW))
     (1128 1128 (:REWRITE CLOSURE-LAWS))
     (976 976 (:TYPE-PRESCRIPTION UNIT-P))
     (891 99 (:REWRITE ZERO-DIVISOR-LAW))
     (681 44 (:REWRITE DIVIDES-PP-SUFF))
     (455 91
          (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (417 182
          (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
     (417 123 (:REWRITE DIVIDES-P-SUFF))
     (345 123
          (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (279 279 (:TYPE-PRESCRIPTION BEZOUT))
     (262 76 (:REWRITE DEFAULT-CAR))
     (180 20 (:REWRITE ASSOCIATE-PP-UNIT-PP))
     (138 45 (:REWRITE DEFAULT-CDR))
     (132 44 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (132 44 (:REWRITE PROJECTION-LAWS))
     (112 5
          (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
     (59 38 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
     (44 44 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (44 44 (:REWRITE RIGHT-UNICITY-LAWS))
     (44 44 (:REWRITE NULLITY-LAWS))
     (40 32
         (:REWRITE CLOSURE-LAWS-FOR-++_E-&-**_E))
     (38 38 (:TYPE-PRESCRIPTION NATP-SIZE))
     (34 34 (:REWRITE GCD-PP-NECC))
     (20 20 (:REWRITE GCD-PP-ASSOCIATES-PP))
     (12 8 (:REWRITE REDUCIBLE-PP-SUFF))
     (10 4 (:LINEAR SIZE->=-SIZE-1_E))
     (8 8 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
     (6 6
        (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
     (1 1 (:REWRITE |1_E-0_E|)))
(EDP-LINEAR-COMBINATION
     (457 118 (:REWRITE UNIT-P-IMPLIES-EDP))
     (287 18 (:DEFINITION UNIT-P))
     (233 18 (:DEFINITION DIVIDES-P))
     (163 62
          (:REWRITE UNIT-ASSOCIATES-PP-REFINES-ASSOCIATES-PP-LEMMA-1))
     (151 59 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (141 53 (:REWRITE DIVIDES-PP-SUFF))
     (118 118 (:TYPE-PRESCRIPTION UNIT-P))
     (104 3
          (:REWRITE DIVIDES-PP-IMPLIES-WITNESS=QQ_E))
     (80 3
         (:REWRITE LINEAR-COMBINATION-DIVIDES-PP-GCD))
     (63 36 (:REWRITE EQUIVALENCE-LAW))
     (36 18
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (36 18 (:REWRITE DIVIDES-P-SUFF))
     (12 6
         (:REWRITE DIVIDES-PP-EDP-DIVIDES-PP-WITNESS))
     (9 9 (:REWRITE CLOSURE-LAWS))
     (6 6 (:EQUIVALENCE ==_E-EQUIVALENCE-LAW))
     (3 3
        (:REWRITE CLOSURE-LAWS-FOR-++_E-&-**_E))
     (1 1 (:REWRITE GCD-PP-NECC)))
(PRIME-PROPERTY-LEMMA (9279 828
                            (:REWRITE INVERSE-CANCELLATION-LAWS-**_E))
                      (6256 1432 (:REWRITE UNIT-P-IMPLIES-EDP))
                      (4762 384 (:DEFINITION UNIT-P))
                      (3911 378 (:DEFINITION DIVIDES-P))
                      (1822 195 (:REWRITE UNIT-PP-**_E-INVERSE))
                      (1594 1114 (:REWRITE EQUIVALENCE-LAW))
                      (1432 1432 (:TYPE-PRESCRIPTION UNIT-P))
                      (759 199 (:DEFINITION UNIT-PP))
                      (664 199
                           (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
                      (608 1 (:REWRITE IRREDUCIBLE-PP-GCD=1_E))
                      (575 1 (:DEFINITION IRREDUCIBLE-PP))
                      (479 384 (:REWRITE DIVIDES-P-SUFF))
                      (420 384
                           (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
                      (398 398
                           (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
                      (325 313 (:REWRITE CLOSURE-LAWS))
                      (315 17 (:REWRITE ZERO-DIVISOR-LAW))
                      (277 1 (:DEFINITION REDUCIBLE-PP))
                      (205 205
                           (:REWRITE LINEAR-COMBINATION-DIVIDES-PP-GCD))
                      (196 196 (:TYPE-PRESCRIPTION UNIT-PP))
                      (96 29 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
                      (60 1 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
                      (50 10
                          (:REWRITE DIVIDES-PP-IMPLIES-WITNESS=QQ_E))
                      (31 1
                          (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
                      (18 18 (:REWRITE NULLITY-LAWS))
                      (18 9 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
                      (12 12
                          (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
                      (9 9 (:TYPE-PRESCRIPTION NATP-SIZE))
                      (3 1 (:LINEAR SIZE->=-SIZE-1_E))
                      (1 1 (:TYPE-PRESCRIPTION IRREDUCIBLE-PP))
                      (1 1 (:REWRITE REDUCIBLE-PP-SUFF))
                      (1 1 (:REWRITE GCD-PP-NECC)))
(IRREDUCIBLE-PP-IMPLIES-PRIME-PROPERTY
     (1198 155 (:REWRITE UNIT-P-IMPLIES-EDP))
     (1107 16 (:DEFINITION UNIT-P))
     (1086 18 (:REWRITE DIVIDES-PP-SUFF))
     (1049 452 (:REWRITE EQUIVALENCE-LAW))
     (919 10 (:DEFINITION DIVIDES-P))
     (902 18 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (795 300
          (:REWRITE INVERSE-CANCELLATION-LAWS-**_E))
     (447 20
          (:REWRITE ASSOCIATIVITY-LAWS-FOR-++_E-&-**_E))
     (417 22 (:REWRITE ZERO-DIVISOR-LAW))
     (375 12 (:REWRITE COMMUTATIVITY-2-LAWS))
     (373 373 (:REWRITE CLOSURE-LAWS))
     (184 16 (:REWRITE DIVIDES-P-SUFF))
     (181 10 (:REWRITE DIVIDES-PP-**_E))
     (179 18 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (155 155 (:TYPE-PRESCRIPTION UNIT-P))
     (72 2
         (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
     (61 5 (:REWRITE DIVIDES-P-IMPLIES-RR_E=0))
     (50 14 (:REWRITE PROJECTION-LAWS))
     (49 49
         (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
     (41 16
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (34 5
         (:REWRITE DIVIDES-PP-IMPLIES-RR_E=0-LEMMA-1))
     (32 4 (:LINEAR SIZE->=-SIZE-1_E))
     (30 25 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
     (21 3
         (:REWRITE DIVIDES-PP-IMPLIES-WITNESS=QQ_E))
     (20 20
         (:REWRITE CLOSURE-LAWS-FOR-++_E-&-**_E))
     (18 18 (:TYPE-PRESCRIPTION NATP-SIZE))
     (15 7 (:REWRITE CANCELLATION-LAWS-FOR-**_E))
     (12 12
         (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
     (9 9 (:REWRITE RIGHT-UNICITY-LAWS))
     (9 9 (:REWRITE NULLITY-LAWS))
     (9 3 (:REWRITE ZERO-DIVISOR-LAW-FOR-**_E))
     (1 1 (:REWRITE GCD-PP-NECC))
     (1 1 (:REWRITE |1_E-0_E|)))
(IRREDUCIBLE-P-IMPLIES-PRIME-PROPERTY
     (746 121 (:REWRITE UNIT-P-IMPLIES-EDP))
     (577 19 (:DEFINITION UNIT-P))
     (568 225 (:REWRITE EQUIVALENCE-LAW))
     (557 22 (:REWRITE DIVIDES-P-SUFF))
     (437 174
          (:REWRITE INVERSE-CANCELLATION-LAWS-**_E))
     (280 20 (:REWRITE DIVIDES-PP-**_E))
     (255 24 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (121 121 (:TYPE-PRESCRIPTION UNIT-P))
     (118 14 (:REWRITE ZERO-DIVISOR-LAW))
     (110 4 (:REWRITE DIVIDES-P-IMPLIES-RR_E=0))
     (92 3
         (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
     (83 19
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (58 43 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
     (50 4
         (:REWRITE DIVIDES-PP-IMPLIES-RR_E=0-LEMMA-1))
     (38 4
         (:REWRITE DIVIDES-PP-IMPLIES-WITNESS=QQ_E))
     (36 36 (:TYPE-PRESCRIPTION NATP-SIZE))
     (34 2 (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-P))
     (31 6 (:LINEAR SIZE->=-SIZE-1_E))
     (24 24 (:REWRITE PRIME-PROPERTY-LEMMA))
     (16 16 (:REWRITE NULLITY-LAWS))
     (1 1 (:REWRITE COMMUTATIVITY-LAWS))
     (1 1 (:REWRITE |1_E-0_E|)))
(IRREDUCIBLE-PP-UNIT-ASSOCIATES
     (2964 405 (:REWRITE UNIT-P-IMPLIES-EDP))
     (2765 44 (:DEFINITION UNIT-P))
     (2535 917 (:REWRITE EQUIVALENCE-LAW))
     (2194 24 (:DEFINITION DIVIDES-P))
     (953 45 (:REWRITE ZERO-DIVISOR-LAW))
     (856 850 (:REWRITE CLOSURE-LAWS))
     (567 44 (:REWRITE DIVIDES-P-SUFF))
     (405 405 (:TYPE-PRESCRIPTION UNIT-P))
     (232 20
          (:REWRITE IRREDUCIBLE-PP-IMPLIES-PRIME-PROPERTY))
     (225 13
          (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
     (171 44
          (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (100 10 (:REWRITE DIVIDES-PP-SUFF))
     (84 60 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
     (63 4
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (53 53 (:TYPE-PRESCRIPTION NATP-SIZE))
     (52 10 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (40 40
         (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
     (37 7 (:LINEAR SIZE->=-SIZE-1_E))
     (21 7
         (:REWRITE DIVIDES-PP-IMPLIES-WITNESS=QQ_E))
     (10 10 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (10 10 (:REWRITE PRIME-PROPERTY-LEMMA))
     (9 3
        (:REWRITE ASSOCIATES-PP-REFINES-UNIT-ASSOCIATES-PP-LEMMA-2))
     (8 8
        (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
     (4 4 (:REWRITE RIGHT-UNICITY-LAWS))
     (4 4 (:REWRITE NULLITY-LAWS))
     (1 1 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
     (1 1 (:REWRITE |1_E-0_E|)))
(IRREDUCIBLE-P-UNIT-ASSOCIATES)
(EDP-IRREDUCIBLE-PP)
(DIVIDES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-LEMMA
     (2205 364 (:REWRITE UNIT-P-IMPLIES-EDP))
     (1987 60 (:DEFINITION UNIT-P))
     (1775 48 (:DEFINITION DIVIDES-P))
     (1645 636 (:REWRITE EQUIVALENCE-LAW))
     (1613 87 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (1308 86 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (954 56
          (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
     (644 29 (:REWRITE ZERO-DIVISOR-LAW))
     (640 498 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
     (544 20 (:REWRITE DIVIDES-P-IMPLIES-RR_E=0))
     (380 380 (:TYPE-PRESCRIPTION NATP-SIZE))
     (364 364 (:TYPE-PRESCRIPTION UNIT-P))
     (297 11 (:REWRITE RR_E-1_E-X=0_E))
     (282 20
          (:REWRITE DIVIDES-PP-IMPLIES-RR_E=0-LEMMA-1))
     (222 58 (:LINEAR SIZE->=-SIZE-1_E))
     (222 20
          (:REWRITE DIVIDES-PP-IMPLIES-WITNESS=QQ_E))
     (184 16
          (:REWRITE DIVIDES-PP-MEMBER-UNIT-ASSOCIATE-PP-**_E-LST))
     (178 60 (:REWRITE DIVIDES-P-SUFF))
     (111 3 (:DEFINITION EDP-LISTP))
     (90 60
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (87 87 (:REWRITE PRIME-PROPERTY-LEMMA))
     (63 63 (:REWRITE NULLITY-LAWS))
     (54 2
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (43 43 (:REWRITE DEFAULT-CAR))
     (28 28
         (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
     (24 7
         (:REWRITE CLOSURE-LAWS-FOR-++_E-&-**_E))
     (16 16
         (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
     (15 15 (:REWRITE DEFAULT-CDR))
     (10 10 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
     (4 4
        (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
     (2 2 (:REWRITE CANCELLATION-LAWS-FOR-**_E))
     (2 2 (:REWRITE |1_E-0_E|))
     (1 1 (:REWRITE PROJECTION-LAWS-1)))
(IRREDUCIBLE-PP-NOT-UNIT-PP)
(DIVIDES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP
     (1181 3
           (:REWRITE IRREDUCIBLE-LISTP-IMPLIES-EDP-LISTP))
     (1173 2 (:DEFINITION IRREDUCIBLE-LISTP))
     (1155 2 (:DEFINITION IRREDUCIBLE-P))
     (1151 72 (:DEFINITION UNIT-P))
     (909 58 (:DEFINITION DIVIDES-P))
     (712 422 (:REWRITE EQUIVALENCE-LAW))
     (653 182 (:REWRITE UNIT-P-IMPLIES-EDP))
     (543 2 (:REWRITE REDUCIBLE-P-SUFF))
     (535 3
          (:REWRITE DIVIDES-PP-MEMBER-UNIT-ASSOCIATE-PP-**_E-LST))
     (442 2 (:DEFINITION REDUCIBLE-P))
     (258 258 (:REWRITE CLOSURE-LAWS))
     (225 225 (:TYPE-PRESCRIPTION UNIT-P))
     (224 1 (:DEFINITION **_E-LST))
     (210 72 (:REWRITE DIVIDES-P-SUFF))
     (165 12 (:REWRITE ZERO-DIVISOR-LAW))
     (98 72
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (67 3 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (43 2
         (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
     (28 28
         (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
     (28 3 (:REWRITE DIVIDES-PP-SUFF))
     (28 1 (:REWRITE DIVIDES-P-IMPLIES-RR_E=0))
     (20 1 (:DEFINITION IRREDUCIBLE-LISTP-1))
     (19 1
         (:REWRITE DIVIDES-PP-IMPLIES-RR_E=0-LEMMA-1))
     (16 1
         (:REWRITE DIVIDES-PP-IMPLIES-WITNESS=QQ_E))
     (14 9 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
     (11 11
         (:TYPE-PRESCRIPTION IRREDUCIBLE-LISTP))
     (9 9 (:TYPE-PRESCRIPTION NATP-SIZE))
     (8 4 (:DEFINITION MV-NTH))
     (7 7 (:REWRITE DEFAULT-CAR))
     (6 6
        (:REWRITE IRREDUCIBLE-PP-IMPLIES-PRIME-PROPERTY))
     (6 6 (:REWRITE DEFAULT-CDR))
     (6 2 (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-P))
     (3 3 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (3 3 (:REWRITE PRIME-PROPERTY-LEMMA))
     (3 3 (:REWRITE EDP-**_E-LST))
     (3 1 (:LINEAR SIZE->=-SIZE-1_E))
     (2 2 (:REWRITE RIGHT-UNICITY-LAWS))
     (2 2 (:REWRITE REDUCIBLE-P-SUFF-2))
     (2 2 (:REWRITE NULLITY-LAWS)))
(EDP-UNIT-ASSOCIATES-PP-WITNESS
     (1193 156 (:REWRITE UNIT-P-IMPLIES-EDP))
     (1143 21 (:DEFINITION UNIT-P))
     (1065 400 (:REWRITE EQUIVALENCE-LAW))
     (1054 11 (:DEFINITION DIVIDES-P))
     (457 20 (:REWRITE ZERO-DIVISOR-LAW))
     (365 365 (:REWRITE CLOSURE-LAWS))
     (217 1
          (:REWRITE IRREDUCIBLE-PP-UNIT-ASSOCIATES))
     (198 2
          (:REWRITE IRREDUCIBLE-PP-IMPLIES-PRIME-PROPERTY))
     (156 156 (:TYPE-PRESCRIPTION UNIT-P))
     (142 2 (:DEFINITION IRREDUCIBLE-PP))
     (88 2 (:DEFINITION REDUCIBLE-PP))
     (86 21 (:REWRITE DIVIDES-P-SUFF))
     (52 2
         (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
     (38 21
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (28 18 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
     (24 24
         (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
     (19 7
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (18 18 (:TYPE-PRESCRIPTION NATP-SIZE))
     (14 14
         (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
     (11 1 (:REWRITE DIVIDES-PP-SUFF))
     (8 4 (:DEFINITION MV-NTH))
     (4 2 (:LINEAR SIZE->=-SIZE-1_E))
     (3 3
        (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
     (3 1 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (2 2 (:TYPE-PRESCRIPTION IRREDUCIBLE-PP))
     (2 2 (:TYPE-PRESCRIPTION DIVIDES-PP))
     (2 2 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
     (2 2 (:REWRITE REDUCIBLE-PP-SUFF))
     (2 2 (:REWRITE DEFAULT-CDR))
     (2 2 (:REWRITE DEFAULT-CAR))
     (1 1 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
     (1 1 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (1 1 (:REWRITE RIGHT-UNICITY-LAWS))
     (1 1 (:REWRITE PRIME-PROPERTY-LEMMA))
     (1 1 (:REWRITE NULLITY-LAWS)))
(==_E-**_E-UNIT-ASSOCIATES-PP-WITNESS
     (1499 208 (:REWRITE UNIT-P-IMPLIES-EDP))
     (1398 30 (:DEFINITION UNIT-P))
     (1272 20 (:DEFINITION DIVIDES-P))
     (1213 482 (:REWRITE EQUIVALENCE-LAW))
     (492 23 (:REWRITE ZERO-DIVISOR-LAW))
     (421 5 (:DEFINITION IRREDUCIBLE-PP))
     (414 414 (:REWRITE CLOSURE-LAWS))
     (347 46
          (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
     (279 8
          (:REWRITE IRREDUCIBLE-PP-UNIT-ASSOCIATES))
     (271 23
          (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (229 5 (:DEFINITION REDUCIBLE-PP))
     (210 8
          (:REWRITE IRREDUCIBLE-PP-IMPLIES-PRIME-PROPERTY))
     (208 208 (:TYPE-PRESCRIPTION UNIT-P))
     (113 30 (:REWRITE DIVIDES-P-SUFF))
     (91 5
         (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
     (55 30
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (48 31 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
     (43 5 (:REWRITE REDUCIBLE-PP-SUFF))
     (32 4 (:REWRITE DIVIDES-PP-SUFF))
     (31 31 (:TYPE-PRESCRIPTION NATP-SIZE))
     (26 26
         (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
     (20 10 (:DEFINITION MV-NTH))
     (15 15 (:TYPE-PRESCRIPTION IRREDUCIBLE-PP))
     (12 12 (:TYPE-PRESCRIPTION DIVIDES-PP))
     (9 4 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (8 8 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
     (7 3 (:LINEAR SIZE->=-SIZE-1_E))
     (5 5 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
     (5 5 (:REWRITE DEFAULT-CDR))
     (5 5 (:REWRITE DEFAULT-CAR))
     (4 4 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (4 4 (:REWRITE PRIME-PROPERTY-LEMMA))
     (1 1 (:REWRITE RIGHT-UNICITY-LAWS))
     (1 1 (:REWRITE NULLITY-LAWS)))
(==_E-**_E-UNIT-ASSOCIATES-PP-WITNESS-1
     (2164 347 (:REWRITE UNIT-P-IMPLIES-EDP))
     (2020 56 (:DEFINITION UNIT-P))
     (1874 40 (:DEFINITION DIVIDES-P))
     (1720 659 (:REWRITE EQUIVALENCE-LAW))
     (1568 7 (:DEFINITION **_E-LST))
     (705 29 (:REWRITE ZERO-DIVISOR-LAW))
     (588 582 (:REWRITE CLOSURE-LAWS))
     (581 1
          (:REWRITE IRREDUCIBLE-PP-UNIT-ASSOCIATES))
     (388 388 (:TYPE-PRESCRIPTION UNIT-P))
     (306 1
          (:REWRITE DIVIDES-PP-MEMBER-UNIT-ASSOCIATE-PP-**_E-LST))
     (249 6
          (:REWRITE INVERSE-CANCELLATION-LAWS-**_E))
     (220 4 (:DEFINITION IRREDUCIBLE-PP))
     (200 2
          (:REWRITE IRREDUCIBLE-PP-IMPLIES-PRIME-PROPERTY))
     (187 2
          (:REWRITE IRREDUCIBLE-LISTP-IMPLIES-EDP-LISTP))
     (181 2 (:DEFINITION IRREDUCIBLE-LISTP))
     (167 2 (:DEFINITION IRREDUCIBLE-P))
     (166 1 (:DEFINITION EDP-LISTP))
     (134 4 (:DEFINITION REDUCIBLE-PP))
     (120 56 (:REWRITE DIVIDES-P-SUFF))
     (98 56
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (98 2
         (:REWRITE IRREDUCIBLE-LISTP-1-IMPLIES-EDP-LISTP))
     (92 2 (:DEFINITION IRREDUCIBLE-LISTP-1))
     (70 2 (:DEFINITION REDUCIBLE-P))
     (65 2 (:REWRITE REDUCIBLE-P-SUFF))
     (53 13
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (50 4
         (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
     (47 8
         (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
     (44 44 (:TYPE-PRESCRIPTION UNIT-PP))
     (36 36
         (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
     (33 1 (:REWRITE DIVIDES-PP-SUFF))
     (26 26
         (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
     (25 25 (:REWRITE DEFAULT-CAR))
     (24 12 (:DEFINITION MV-NTH))
     (18 18 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
     (18 18 (:TYPE-PRESCRIPTION NATP-SIZE))
     (18 18 (:REWRITE DEFAULT-CDR))
     (17 1 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (10 10
         (:TYPE-PRESCRIPTION IRREDUCIBLE-LISTP-1))
     (10 10
         (:TYPE-PRESCRIPTION IRREDUCIBLE-LISTP))
     (6 1 (:REWRITE PROJECTION-LAWS))
     (5 5 (:TYPE-PRESCRIPTION EDP-LISTP))
     (4 4 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
     (4 4 (:REWRITE REDUCIBLE-PP-SUFF))
     (4 2 (:LINEAR SIZE->=-SIZE-1_E))
     (4 1 (:REWRITE RIGHT-UNICITY-LAWS))
     (2 2 (:TYPE-PRESCRIPTION IRREDUCIBLE-PP))
     (2 2 (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-P))
     (2 2 (:REWRITE REDUCIBLE-P-SUFF-2))
     (1 1 (:TYPE-PRESCRIPTION DIVIDES-PP))
     (1 1 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
     (1 1 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (1 1 (:REWRITE PRIME-PROPERTY-LEMMA)))
(**_E-IRREDUCIBLE-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP-LEMMA
     (3497 119 (:DEFINITION UNIT-P))
     (3134 527 (:REWRITE UNIT-P-IMPLIES-EDP))
     (3095 85 (:DEFINITION DIVIDES-P))
     (2831 1242 (:REWRITE EQUIVALENCE-LAW))
     (2016 9 (:DEFINITION **_E-LST))
     (1405 1
           (:REWRITE DIVIDES-PP-MEMBER-UNIT-ASSOCIATE-PP-**_E-LST))
     (1179 2
           (:REWRITE IRREDUCIBLE-LISTP-IMPLIES-EDP-LISTP))
     (1173 2 (:DEFINITION IRREDUCIBLE-LISTP))
     (1155 2 (:DEFINITION IRREDUCIBLE-P))
     (1039 53 (:REWRITE ZERO-DIVISOR-LAW))
     (961 955 (:REWRITE CLOSURE-LAWS))
     (793 1 (:DEFINITION EDP-LISTP))
     (570 570 (:TYPE-PRESCRIPTION UNIT-P))
     (543 2 (:REWRITE REDUCIBLE-P-SUFF))
     (448 4 (:DEFINITION IRREDUCIBLE-PP))
     (442 2 (:DEFINITION REDUCIBLE-P))
     (368 2
          (:REWRITE IRREDUCIBLE-PP-IMPLIES-PRIME-PROPERTY))
     (361 119 (:REWRITE DIVIDES-P-SUFF))
     (264 4 (:DEFINITION REDUCIBLE-PP))
     (197 119
          (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (168 2
          (:REWRITE IRREDUCIBLE-LISTP-1-IMPLIES-EDP-LISTP))
     (162 2 (:DEFINITION IRREDUCIBLE-LISTP-1))
     (72 72
         (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
     (60 4
         (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
     (54 54 (:EQUIVALENCE ==_E-EQUIVALENCE-LAW))
     (42 42 (:TYPE-PRESCRIPTION UNIT-PP))
     (36 12
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (29 29 (:REWRITE DEFAULT-CAR))
     (28 18 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
     (24 24
         (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
     (24 12 (:DEFINITION MV-NTH))
     (20 20 (:REWRITE DEFAULT-CDR))
     (18 18 (:TYPE-PRESCRIPTION NATP-SIZE))
     (11 1 (:REWRITE DIVIDES-PP-SUFF))
     (10 10
         (:TYPE-PRESCRIPTION IRREDUCIBLE-LISTP-1))
     (10 10
         (:TYPE-PRESCRIPTION IRREDUCIBLE-LISTP))
     (6 2 (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-P))
     (6 2 (:LINEAR SIZE->=-SIZE-1_E))
     (5 5 (:TYPE-PRESCRIPTION EDP-LISTP))
     (4 4 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
     (4 4 (:REWRITE REDUCIBLE-PP-SUFF))
     (3 1 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (2 2 (:TYPE-PRESCRIPTION IRREDUCIBLE-PP))
     (2 2 (:REWRITE REDUCIBLE-P-SUFF-2))
     (1 1 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (1 1 (:REWRITE RIGHT-UNICITY-LAWS))
     (1 1 (:REWRITE PRIME-PROPERTY-LEMMA))
     (1 1 (:REWRITE NULLITY-LAWS)))
(**_E-IRREDUCIBLE-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP
     (1092 176 (:REWRITE UNIT-P-IMPLIES-EDP))
     (1002 22 (:DEFINITION UNIT-P))
     (950 14 (:DEFINITION DIVIDES-P))
     (888 350 (:REWRITE EQUIVALENCE-LAW))
     (501 3 (:DEFINITION **_E-LST))
     (382 2
          (:REWRITE IRREDUCIBLE-PP-UNIT-ASSOCIATES))
     (373 17 (:REWRITE ZERO-DIVISOR-LAW))
     (313 313 (:REWRITE CLOSURE-LAWS))
     (251 1 (:DEFINITION IRREDUCIBLE-LISTP-1))
     (192 192 (:TYPE-PRESCRIPTION UNIT-P))
     (174 1
          (:REWRITE DIVIDES-PP-MEMBER-UNIT-ASSOCIATE-PP-**_E-LST))
     (103 1 (:REWRITE DIVIDES-PP-SUFF))
     (88 1
         (:REWRITE IRREDUCIBLE-LISTP-IMPLIES-EDP-LISTP))
     (85 1 (:DEFINITION IRREDUCIBLE-LISTP))
     (78 1 (:DEFINITION IRREDUCIBLE-P))
     (74 2
         (:REWRITE IRREDUCIBLE-PP-IMPLIES-PRIME-PROPERTY))
     (69 3
         (:REWRITE ASSOCIATIVITY-LAWS-FOR-++_E-&-**_E))
     (55 8
         (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
     (46 22 (:REWRITE DIVIDES-P-SUFF))
     (45 1
         (:DEFINITION MEMBER-UNIT-ASSOCIATE-PP))
     (38 6
         (:REWRITE INVERSE-CANCELLATION-LAWS-**_E))
     (36 22
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
     (36 2
         (:REWRITE DIVIDES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-LEMMA))
     (35 1 (:DEFINITION REDUCIBLE-P))
     (30 18
         (:REWRITE CLOSURE-LAWS-FOR-++_E-&-**_E))
     (27 1 (:REWRITE REDUCIBLE-P-SUFF))
     (25 9
         (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
     (25 1 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
     (18 18
         (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
     (17 17 (:REWRITE EDP-**_E-LST))
     (16 16
         (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
     (14 9 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
     (10 10 (:REWRITE DEFAULT-CAR))
     (9 9 (:TYPE-PRESCRIPTION NATP-SIZE))
     (9 9 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
     (9 9 (:REWRITE REDUCIBLE-PP-SUFF))
     (9 3 (:REWRITE NULLITY-LAWS))
     (8 2 (:REWRITE RIGHT-UNICITY-LAWS))
     (7 7 (:REWRITE DEFAULT-CDR))
     (6 6 (:REWRITE UNIT-PP-CLOSURE-**_E))
     (6 3
        (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
     (6 1 (:REWRITE ZERO-DIVISOR-LAW-FOR-**_E))
     (5 5
        (:TYPE-PRESCRIPTION IRREDUCIBLE-LISTP))
     (4 2 (:DEFINITION MV-NTH))
     (3 1 (:LINEAR SIZE->=-SIZE-1_E))
     (2 2 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
     (1 1 (:TYPE-PRESCRIPTION EDP-LISTP))
     (1 1 (:REWRITE TRANSITIVITY-DIVIDES-PP))
     (1 1 (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-P))
     (1 1 (:REWRITE REDUCIBLE-P-SUFF-2))
     (1 1 (:REWRITE PRIME-PROPERTY-LEMMA))
     (1 1
        (:REWRITE IRREDUCIBLE-LISTP-1-IMPLIES-EDP-LISTP)))
(**_E-LST-OF-IRREDUCIBLE-LISTP-1-NOT-UNIT-ASSOCIATE-PP-1_E
 (4688 246
       (:REWRITE IRREDUCIBLE-PP-IMPLIES-PRIME-PROPERTY))
 (2849 28
       (:REWRITE IRREDUCIBLE-PP-UNIT-ASSOCIATES))
 (2308 59 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
 (1951 149
       (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
 (1539 15
       (:REWRITE DIVIDES-PP-MEMBER-UNIT-ASSOCIATE-PP-**_E-LST))
 (1162 367 (:REWRITE UNIT-P-IMPLIES-EDP))
 (922 593 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
 (775 775 (:TYPE-PRESCRIPTION UNIT-P))
 (655 16
      (:REWRITE IRREDUCIBLE-LISTP-IMPLIES-EDP-LISTP))
 (635 172
      (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
 (613 10 (:DEFINITION IRREDUCIBLE-LISTP))
 (593 593 (:TYPE-PRESCRIPTION NATP-SIZE))
 (513 10 (:DEFINITION IRREDUCIBLE-P))
 (478 123
      (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
 (442 14
      (:DEFINITION MEMBER-UNIT-ASSOCIATE-PP))
 (387 183
      (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
 (356 356 (:TYPE-PRESCRIPTION IRREDUCIBLE-PP))
 (344 344
      (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
 (298 27
      (:REWRITE DIVIDES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP))
 (298 27
      (:REWRITE DIVIDES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-LEMMA))
 (253 10 (:REWRITE REDUCIBLE-P-SUFF))
 (170 10 (:DEFINITION REDUCIBLE-P))
 (163 65 (:LINEAR SIZE->=-SIZE-1_E))
 (157 86 (:REWRITE EQUIVALENCE-LAW))
 (129 1 (:DEFINITION EDP-LISTP))
 (123 123 (:REWRITE PRIME-PROPERTY-LEMMA))
 (116 116 (:REWRITE TRANSITIVITY-DIVIDES-PP))
 (93 93 (:REWRITE DEFAULT-CAR))
 (88 82 (:REWRITE NULLITY-LAWS))
 (81 81 (:TYPE-PRESCRIPTION UNIT-PP))
 (80 80 (:REWRITE UNIT-PP-1_E))
 (69 3
     (:REWRITE ASSOCIATIVITY-LAWS-FOR-++_E-&-**_E))
 (66 66
     (:TYPE-PRESCRIPTION MEMBER-UNIT-ASSOCIATE-PP))
 (65 65 (:REWRITE DEFAULT-CDR))
 (65 65 (:REWRITE |1_E-0_E|))
 (60 16
     (:REWRITE IRREDUCIBLE-LISTP-1-IMPLIES-EDP-LISTP))
 (59 59 (:REWRITE REDUCIBLE-PP-SUFF))
 (56 56
     (:TYPE-PRESCRIPTION IRREDUCIBLE-LISTP))
 (56 8 (:REWRITE UNIT-PP-CLOSURE-**_E))
 (40 20 (:DEFINITION MV-NTH))
 (38 6
     (:REWRITE INVERSE-CANCELLATION-LAWS-**_E))
 (30 18
     (:REWRITE CLOSURE-LAWS-FOR-++_E-&-**_E))
 (28 28 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
 (27
    27
    (:REWRITE **_E-IRREDUCIBLE-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP))
 (20 17
     (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
 (19 19 (:TYPE-PRESCRIPTION EDP-LISTP))
 (15
   15
   (:REWRITE
        **_E-IRREDUCIBLE-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP-LEMMA))
 (10 10
     (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-P))
 (10 10 (:REWRITE REDUCIBLE-P-SUFF-2))
 (6 1 (:REWRITE ZERO-DIVISOR-LAW-FOR-**_E)))
(IRREDUCIBLE-LISTP-1-DELETE-ONE-UNIT-ASSOCIATE-PP
 (4107 745 (:REWRITE UNIT-P-IMPLIES-EDP))
 (3650 134 (:DEFINITION UNIT-P))
 (3305 116 (:DEFINITION DIVIDES-P))
 (2815 1126 (:REWRITE EQUIVALENCE-LAW))
 (1033 54 (:REWRITE ZERO-DIVISOR-LAW))
 (858 28
      (:REWRITE IRREDUCIBLE-PP-IMPLIES-PRIME-PROPERTY))
 (745 745 (:TYPE-PRESCRIPTION UNIT-P))
 (666 9
      (:REWRITE DIVIDES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP))
 (666 9
      (:REWRITE DIVIDES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-LEMMA))
 (578 58
      (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
 (255 134 (:REWRITE DIVIDES-P-SUFF))
 (203 134
      (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
 (174 58
      (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
 (172 14 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
 (116 116
      (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
 (58 58 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
 (58 58 (:REWRITE REDUCIBLE-PP-SUFF))
 (56 36 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
 (36 36 (:TYPE-PRESCRIPTION NATP-SIZE))
 (36 36
     (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
 (28 28 (:REWRITE DEFAULT-CAR))
 (14 14 (:REWRITE TRANSITIVITY-DIVIDES-PP))
 (14 14 (:REWRITE PRIME-PROPERTY-LEMMA))
 (14 14 (:REWRITE DEFAULT-CDR))
 (13 13 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
 (10 4 (:LINEAR SIZE->=-SIZE-1_E))
 (9
   9
   (:REWRITE **_E-IRREDUCIBLE-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP)))
(UNIT-ASSOCIATES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP
 (1329 226 (:REWRITE UNIT-P-IMPLIES-EDP))
 (1231 31 (:DEFINITION UNIT-P))
 (1139 19 (:DEFINITION DIVIDES-P))
 (1088 375 (:REWRITE EQUIVALENCE-LAW))
 (799 5 (:DEFINITION **_E-LST))
 (437 17 (:REWRITE ZERO-DIVISOR-LAW))
 (236 2 (:DEFINITION IRREDUCIBLE-LISTP-1))
 (235 235 (:TYPE-PRESCRIPTION UNIT-P))
 (208 1
      (:REWRITE DIVIDES-PP-MEMBER-UNIT-ASSOCIATE-PP-**_E-LST))
 (110 4
      (:REWRITE IRREDUCIBLE-PP-IMPLIES-PRIME-PROPERTY))
 (105 9
      (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
 (89 1
     (:DEFINITION MEMBER-UNIT-ASSOCIATE-PP))
 (85 31 (:REWRITE DIVIDES-P-SUFF))
 (85 4
     (:REWRITE IRREDUCIBLE-LISTP-IMPLIES-EDP-LISTP))
 (76 1 (:DEFINITION IRREDUCIBLE-LISTP))
 (74 31
     (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
 (69 1 (:DEFINITION IRREDUCIBLE-P))
 (58 10
     (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
 (51 2
     (:REWRITE DIVIDES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-LEMMA))
 (35 1 (:DEFINITION REDUCIBLE-P))
 (27 27 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
 (27 27 (:TYPE-PRESCRIPTION NATP-SIZE))
 (24 24
     (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
 (20 20
     (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
 (18 2 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
 (18 1 (:REWRITE REDUCIBLE-P-SUFF))
 (16 16 (:REWRITE DEFAULT-CAR))
 (12 1 (:DEFINITION EDP-LISTP))
 (11 11 (:REWRITE DEFAULT-CDR))
 (11 1
     (:REWRITE IRREDUCIBLE-PP-UNIT-ASSOCIATES))
 (10 10 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
 (10 10 (:REWRITE REDUCIBLE-PP-SUFF))
 (8 8
    (:TYPE-PRESCRIPTION IRREDUCIBLE-LISTP))
 (7 7 (:TYPE-PRESCRIPTION EDP-LISTP))
 (7 3 (:LINEAR SIZE->=-SIZE-1_E))
 (6 4
    (:REWRITE IRREDUCIBLE-LISTP-1-IMPLIES-EDP-LISTP))
 (4 2 (:DEFINITION MV-NTH))
 (3 3
    (:REWRITE **_E-IRREDUCIBLE-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP))
 (2 2 (:REWRITE TRANSITIVITY-DIVIDES-PP))
 (2 2 (:REWRITE PRIME-PROPERTY-LEMMA))
 (1 1 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
 (1 1 (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-P))
 (1 1 (:REWRITE REDUCIBLE-P-SUFF-2))
 (1
  1
  (:REWRITE
       **_E-IRREDUCIBLE-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP-LEMMA)))
(REDUCIBLE-PP-**_E (948 248 (:REWRITE UNIT-P-IMPLIES-EDP))
                   (658 74 (:DEFINITION UNIT-P))
                   (492 74 (:DEFINITION DIVIDES-P))
                   (248 248 (:TYPE-PRESCRIPTION UNIT-P))
                   (245 152
                        (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
                   (230 30 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
                   (184 76
                        (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
                   (132 132 (:REWRITE EQUIVALENCE-LAW))
                   (96 4 (:DEFINITION IRREDUCIBLE-PP))
                   (92 74 (:REWRITE DIVIDES-P-SUFF))
                   (74 74
                       (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
                   (73 18 (:REWRITE UNIT-PP-CLOSURE-**_E))
                   (57 5 (:DEFINITION UNIT-PP))
                   (36 12
                       (:REWRITE CANCELLATION-LAWS-FOR-**_E))
                   (20 20 (:REWRITE CLOSURE-LAWS))
                   (20 10
                       (:REWRITE IRREDUCIBLE-PP-IMPLIES-PRIME-PROPERTY))
                   (19 19 (:TYPE-PRESCRIPTION IRREDUCIBLE-PP))
                   (16 6 (:REWRITE ZERO-DIVISOR-LAW-FOR-**_E))
                   (11 5 (:REWRITE DIVIDES-PP-SUFF))
                   (6 5 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
                   (5 5 (:TYPE-PRESCRIPTION DIVIDES-PP))
                   (5 5 (:REWRITE TRANSITIVITY-DIVIDES-PP))
                   (5 5 (:REWRITE REDUCIBLE-PP-SUFF))
                   (5 5 (:REWRITE PRIME-PROPERTY-LEMMA))
                   (4 4
                      (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP)))
(REDUCIBLE-PP-**_E-1)
(REDUCIBLE-PP-**_E-LST (400 107 (:REWRITE UNIT-P-IMPLIES-EDP))
                       (271 29 (:DEFINITION UNIT-P))
                       (199 29 (:DEFINITION DIVIDES-P))
                       (107 107 (:TYPE-PRESCRIPTION UNIT-P))
                       (100 11
                            (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
                       (65 31
                           (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
                       (65 24 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
                       (62 62
                           (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
                       (56 56 (:REWRITE EQUIVALENCE-LAW))
                       (52 52 (:EQUIVALENCE ==_E-EQUIVALENCE-LAW))
                       (51 51 (:REWRITE DEFAULT-CAR))
                       (43 29 (:REWRITE DIVIDES-P-SUFF))
                       (42 27 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
                       (41 41 (:REWRITE DEFAULT-CDR))
                       (30 30 (:REWRITE REDUCIBLE-PP-SUFF))
                       (29 29
                           (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
                       (27 27 (:TYPE-PRESCRIPTION NATP-SIZE))
                       (14 14 (:REWRITE EDP-**_E-LST))
                       (14 14 (:REWRITE CLOSURE-LAWS))
                       (6 6 (:REWRITE UNIT-PP-CLOSURE-**_E))
                       (6 3 (:LINEAR SIZE->=-SIZE-1_E)))
(NOT-IRREDUCIBLE-PP-1_E)
(IRREDUCIBLE-LISTP-1-IRREDUCIBLE-PP-MEMBER-UNIT-ASSOCIATE-PP
 (63 7
     (:REWRITE IRREDUCIBLE-PP-UNIT-ASSOCIATES))
 (59 12
     (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
 (22 11 (:REWRITE UNIT-P-IMPLIES-EDP))
 (16 16 (:REWRITE DEFAULT-CAR))
 (14 14 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
 (14 14 (:TYPE-PRESCRIPTION DIVIDES-PP))
 (14 14
     (:REWRITE IRREDUCIBLE-PP-IMPLIES-PRIME-PROPERTY))
 (11 11 (:TYPE-PRESCRIPTION UNIT-P))
 (10 3 (:LINEAR SIZE->=-SIZE-1_E))
 (8 8
    (:REWRITE UNIT-ASSOCIATES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP))
 (8 8
    (:REWRITE DIVIDES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP))
 (8 8
    (:REWRITE DIVIDES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-LEMMA))
 (8 8
    (:REWRITE **_E-IRREDUCIBLE-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP))
 (7 7 (:TYPE-PRESCRIPTION NATP-SIZE))
 (7 7 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
 (7 7 (:REWRITE TRANSITIVITY-DIVIDES-PP))
 (7 7 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
 (7 7 (:REWRITE PRIME-PROPERTY-LEMMA))
 (7 7 (:REWRITE DIVIDES-PP-SUFF))
 (4 4 (:REWRITE DEFAULT-CDR)))
(UNIT-ASSOCIATES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP-1
 (3358 10 (:DEFINITION IRREDUCIBLE-PP))
 (2324 370 (:REWRITE UNIT-P-IMPLIES-EDP))
 (2176 54 (:DEFINITION UNIT-P))
 (2088 10 (:DEFINITION REDUCIBLE-PP))
 (2080 2 (:DEFINITION IRREDUCIBLE-LISTP-1))
 (2045 38 (:DEFINITION DIVIDES-P))
 (1870 730 (:REWRITE EQUIVALENCE-LAW))
 (1289 38 (:DEFINITION UNIT-PP))
 (992 82
      (:REWRITE IRREDUCIBLE-PP-IMPLIES-PRIME-PROPERTY))
 (817 2
      (:REWRITE IRREDUCIBLE-PP-UNIT-ASSOCIATES))
 (766 38 (:REWRITE ZERO-DIVISOR-LAW))
 (704 704 (:REWRITE CLOSURE-LAWS))
 (550 26
      (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
 (480 480 (:EQUIVALENCE ==_E-EQUIVALENCE-LAW))
 (446
     3
     (:REWRITE UNIT-ASSOCIATES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP))
 (438 39 (:REWRITE DIVIDES-PP-SUFF))
 (388 388 (:TYPE-PRESCRIPTION UNIT-P))
 (352 2
      (:REWRITE DIVIDES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-LEMMA))
 (297 10 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
 (242 162 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
 (162 162 (:TYPE-PRESCRIPTION NATP-SIZE))
 (160 3
      (:REWRITE IRREDUCIBLE-LISTP-IMPLIES-EDP-LISTP))
 (152 2 (:DEFINITION IRREDUCIBLE-LISTP))
 (138 2 (:DEFINITION IRREDUCIBLE-P))
 (121 39 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
 (104 54 (:REWRITE DIVIDES-P-SUFF))
 (104 38
      (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
 (92 54
     (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
 (76 76
     (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
 (70 2 (:DEFINITION REDUCIBLE-P))
 (48 24 (:DEFINITION MV-NTH))
 (48 18 (:LINEAR SIZE->=-SIZE-1_E))
 (43 43 (:TYPE-PRESCRIPTION UNIT-PP))
 (42 42
     (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
 (41 41 (:REWRITE PRIME-PROPERTY-LEMMA))
 (39 39 (:REWRITE TRANSITIVITY-DIVIDES-PP))
 (36 2 (:REWRITE REDUCIBLE-P-SUFF))
 (31 31
     (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
 (30 27 (:REWRITE RIGHT-UNICITY-LAWS))
 (30 27 (:REWRITE NULLITY-LAWS))
 (24 24 (:REWRITE DEFAULT-CAR))
 (21 21 (:REWRITE EDP-**_E-LST))
 (20 20 (:REWRITE DEFAULT-CDR))
 (11 11
     (:TYPE-PRESCRIPTION IRREDUCIBLE-LISTP))
 (10 10 (:REWRITE REDUCIBLE-PP-SUFF))
 (5 5 (:REWRITE REDUCIBLE-PP-**_E-LST))
 (3
   3
   (:REWRITE
        **_E-IRREDUCIBLE-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP-LEMMA))
 (3 3
    (:REWRITE **_E-IRREDUCIBLE-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP))
 (2 2 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
 (2 2 (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-P))
 (2 2 (:REWRITE REDUCIBLE-P-SUFF-2))
 (2 2 (:REWRITE PROJECTION-LAWS)))
(MEMBER-UNIT-ASSOCIATE-PP-EDP-LISTP-IMPLIES-EDP
 (15445 9
        (:REWRITE IRREDUCIBLE-LISTP-IMPLIES-EDP-LISTP))
 (15423 10 (:DEFINITION IRREDUCIBLE-LISTP))
 (15329 6576 (:REWRITE EQUIVALENCE-LAW))
 (15074 409 (:DEFINITION UNIT-P))
 (14088 10 (:DEFINITION IRREDUCIBLE-P))
 (11243 325 (:DEFINITION DIVIDES-P))
 (9646 2608 (:REWRITE UNIT-P-IMPLIES-EDP))
 (7995 6 (:DEFINITION REDUCIBLE-P))
 (6877 9
       (:REWRITE IRREDUCIBLE-LISTP-1-IMPLIES-EDP-LISTP))
 (6855 10 (:DEFINITION IRREDUCIBLE-LISTP-1))
 (6698 70 (:DEFINITION IRREDUCIBLE-PP))
 (5045 5045 (:REWRITE CLOSURE-LAWS))
 (5020 228
       (:REWRITE IRREDUCIBLE-PP-IMPLIES-PRIME-PROPERTY))
 (4832 104 (:DEFINITION UNIT-PP))
 (4712 292 (:REWRITE ZERO-DIVISOR-LAW))
 (4370 28 (:DEFINITION REDUCIBLE-PP))
 (3903 409 (:REWRITE DIVIDES-P-SUFF))
 (3689 6 (:REWRITE REDUCIBLE-P-SUFF))
 (2688 2688 (:TYPE-PRESCRIPTION UNIT-P))
 (1657 1657
       (:EQUIVALENCE ==_E-EQUIVALENCE-LAW))
 (1609 114 (:REWRITE DIVIDES-PP-SUFF))
 (1298 102
       (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
 (1164 409
       (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
 (1055 28 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
 (672 438 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
 (438 438 (:TYPE-PRESCRIPTION NATP-SIZE))
 (320 320 (:TYPE-PRESCRIPTION IRREDUCIBLE-PP))
 (298 114
      (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
 (282 104
      (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
 (267 267 (:TYPE-PRESCRIPTION DIVIDES-PP))
 (231 7
      (:REWRITE IRREDUCIBLE-PP-UNIT-ASSOCIATES))
 (208 208
      (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
 (194 194
      (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
 (190 84 (:DEFINITION MV-NTH))
 (177 177
      (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
 (140 10
      (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-P))
 (124 124 (:REWRITE DEFAULT-CAR))
 (114 114 (:REWRITE TRANSITIVITY-DIVIDES-PP))
 (114 114 (:REWRITE PRIME-PROPERTY-LEMMA))
 (104
     8
     (:REWRITE UNIT-ASSOCIATES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP))
 (104 8
      (:REWRITE DIVIDES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP))
 (104 8
      (:REWRITE DIVIDES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-LEMMA))
 (102 102
      (:REWRITE IRREDUCIBLE-LISTP-1-IRREDUCIBLE-PP-MEMBER-UNIT-ASSOCIATE-PP))
 (96 46 (:LINEAR SIZE->=-SIZE-1_E))
 (77 77 (:REWRITE RIGHT-UNICITY-LAWS))
 (77 77 (:REWRITE NULLITY-LAWS))
 (74 74 (:REWRITE DEFAULT-CDR))
 (44 44 (:TYPE-PRESCRIPTION UNIT-PP))
 (31 31
     (:TYPE-PRESCRIPTION IRREDUCIBLE-LISTP-1))
 (31 31
     (:TYPE-PRESCRIPTION IRREDUCIBLE-LISTP))
 (28 28 (:REWRITE RIGHT-UNICITY-LAW-FOR-*_E))
 (28 28 (:REWRITE REDUCIBLE-PP-SUFF))
 (28 28 (:REWRITE LEFT-UNICITY-LAWS))
 (8
   8
   (:REWRITE UNIT-ASSOCIATES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP-1))
 (8 8
    (:REWRITE **_E-IRREDUCIBLE-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP))
 (7 7 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
 (6 6 (:TYPE-PRESCRIPTION REDUCIBLE-PP))
 (6 6 (:REWRITE REDUCIBLE-P-SUFF-2)))
(UNIT-PP-UNIT-ASSOCIATES-PP-WITNESS
   (832 104 (:REWRITE UNIT-P-IMPLIES-EDP))
   (786 16 (:DEFINITION UNIT-P))
   (695 226 (:REWRITE EQUIVALENCE-LAW))
   (691 10 (:DEFINITION DIVIDES-P))
   (266 11 (:REWRITE ZERO-DIVISOR-LAW))
   (253 3
        (:REWRITE IRREDUCIBLE-PP-UNIT-ASSOCIATES))
   (218 4
        (:REWRITE IRREDUCIBLE-PP-IMPLIES-PRIME-PROPERTY))
   (216 216 (:REWRITE CLOSURE-LAWS))
   (156 2 (:DEFINITION IRREDUCIBLE-PP))
   (105 105
        (:REWRITE MEMBER-UNIT-ASSOCIATE-PP-EDP-LISTP-IMPLIES-EDP))
   (104 104 (:TYPE-PRESCRIPTION UNIT-P))
   (96 2 (:DEFINITION REDUCIBLE-PP))
   (89 16 (:REWRITE DIVIDES-P-SUFF))
   (73 8
       (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
   (52 2
       (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
   (45 45 (:EQUIVALENCE ==_E-EQUIVALENCE-LAW))
   (32 16
       (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
   (31 3
       (:REWRITE EDP-UNIT-ASSOCIATES-PP-WITNESS))
   (28 18 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
   (18 18 (:TYPE-PRESCRIPTION NATP-SIZE))
   (18 2 (:REWRITE DIVIDES-PP-SUFF))
   (16 16
       (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
   (16 16
       (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
   (8 4 (:DEFINITION MV-NTH))
   (5 5 (:TYPE-PRESCRIPTION DIVIDES-PP))
   (5 2 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
   (4 4 (:TYPE-PRESCRIPTION IRREDUCIBLE-PP))
   (4 2 (:LINEAR SIZE->=-SIZE-1_E))
   (3 3 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
   (2 2 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
   (2 2 (:REWRITE TRANSITIVITY-DIVIDES-PP))
   (2 2 (:REWRITE REDUCIBLE-PP-SUFF))
   (2 2 (:REWRITE PRIME-PROPERTY-LEMMA))
   (2 2
      (:REWRITE IRREDUCIBLE-LISTP-1-IRREDUCIBLE-PP-MEMBER-UNIT-ASSOCIATE-PP))
   (2 2 (:REWRITE DEFAULT-CDR))
   (2 2 (:REWRITE DEFAULT-CAR))
   (2 2
      (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
   (1 1 (:REWRITE RIGHT-UNICITY-LAWS))
   (1 1 (:REWRITE NULLITY-LAWS)))
(==_E-**_E-UNIT-ASSOCIATES-PP-WITNESS-A
   (626 1
        (:REWRITE IRREDUCIBLE-PP-UNIT-ASSOCIATES))
   (580 24
        (:REWRITE IRREDUCIBLE-PP-IMPLIES-PRIME-PROPERTY))
   (464 4 (:DEFINITION IRREDUCIBLE-PP))
   (462 60 (:REWRITE UNIT-P-IMPLIES-EDP))
   (421 11 (:DEFINITION UNIT-P))
   (382 11 (:DEFINITION UNIT-PP))
   (352 124 (:REWRITE EQUIVALENCE-LAW))
   (293 9 (:DEFINITION DIVIDES-P))
   (214 2 (:DEFINITION REDUCIBLE-PP))
   (170 12 (:REWRITE DIVIDES-PP-SUFF))
   (134 134 (:REWRITE CLOSURE-LAWS))
   (119 11 (:REWRITE DIVIDES-P-SUFF))
   (115 6 (:REWRITE ZERO-DIVISOR-LAW))
   (104 4
        (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
   (70 70
       (:REWRITE MEMBER-UNIT-ASSOCIATE-PP-EDP-LISTP-IMPLIES-EDP))
   (60 60 (:TYPE-PRESCRIPTION UNIT-P))
   (56 36 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
   (50 4 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
   (37 6
       (:REWRITE INVERSE-CANCELLATION-LAWS-**_E))
   (36 36 (:TYPE-PRESCRIPTION NATP-SIZE))
   (34 12 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
   (31 11
       (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
   (25 11
       (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
   (24 24 (:TYPE-PRESCRIPTION IRREDUCIBLE-PP))
   (22 22
       (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
   (20 20 (:TYPE-PRESCRIPTION DIVIDES-PP))
   (13 13 (:TYPE-PRESCRIPTION UNIT-PP))
   (12 12 (:REWRITE TRANSITIVITY-DIVIDES-PP))
   (12 12 (:REWRITE PRIME-PROPERTY-LEMMA))
   (10 10 (:REWRITE RIGHT-UNICITY-LAWS))
   (9 9 (:REWRITE NULLITY-LAWS))
   (8 8
      (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
   (8 4 (:LINEAR SIZE->=-SIZE-1_E))
   (8 4 (:DEFINITION MV-NTH))
   (6 2 (:REWRITE PROJECTION-LAWS))
   (4 4
      (:REWRITE IRREDUCIBLE-LISTP-1-IRREDUCIBLE-PP-MEMBER-UNIT-ASSOCIATE-PP))
   (2 2 (:REWRITE REDUCIBLE-PP-SUFF))
   (2 2 (:REWRITE DEFAULT-CDR))
   (2 2 (:REWRITE DEFAULT-CAR))
   (1 1 (:REWRITE UNIT-ASSOCIATES-PP-SUFF)))
(UNIT-ASSOCIATES-PP-**_E-1
   (1104 193 (:REWRITE UNIT-P-IMPLIES-EDP))
   (1101 2
         (:REWRITE IRREDUCIBLE-PP-UNIT-ASSOCIATES))
   (911 25 (:DEFINITION UNIT-P))
   (818 8
        (:REWRITE IRREDUCIBLE-PP-IMPLIES-PRIME-PROPERTY))
   (778 231 (:REWRITE EQUIVALENCE-LAW))
   (680 8 (:DEFINITION IRREDUCIBLE-PP))
   (626 19 (:DEFINITION DIVIDES-P))
   (416 12 (:DEFINITION REDUCIBLE-PP))
   (363 2 (:REWRITE DIVIDES-PP-**_E))
   (270 25 (:REWRITE DIVIDES-P-SUFF))
   (224 208 (:REWRITE CLOSURE-LAWS))
   (213 213
        (:REWRITE MEMBER-UNIT-ASSOCIATE-PP-EDP-LISTP-IMPLIES-EDP))
   (197 4 (:REWRITE DIVIDES-PP-SUFF))
   (193 193 (:TYPE-PRESCRIPTION UNIT-P))
   (191 8 (:REWRITE ZERO-DIVISOR-LAW))
   (166 48
        (:REWRITE INVERSE-CANCELLATION-LAWS-**_E))
   (140 12 (:REWRITE REDUCIBLE-PP-**_E))
   (114 8
        (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
   (105 39
        (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
   (101 10
        (:REWRITE ASSOCIATIVITY-LAWS-FOR-++_E-&-**_E))
   (99 25
       (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
   (78 78
       (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
   (48 24 (:DEFINITION MV-NTH))
   (46 36 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
   (43 4 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
   (36 36 (:TYPE-PRESCRIPTION NATP-SIZE))
   (22 6 (:REWRITE UNIT-PP-CLOSURE-**_E))
   (22 6 (:REWRITE REDUCIBLE-PP-**_E-1))
   (20 20
       (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
   (15 5 (:REWRITE ZERO-DIVISOR-LAW-FOR-**_E))
   (12 12 (:TYPE-PRESCRIPTION REDUCIBLE-PP))
   (12 12 (:REWRITE REDUCIBLE-PP-SUFF))
   (12 12 (:REWRITE DEFAULT-CDR))
   (12 12 (:REWRITE DEFAULT-CAR))
   (8 8 (:TYPE-PRESCRIPTION IRREDUCIBLE-PP))
   (8 8 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
   (8 8
      (:REWRITE IRREDUCIBLE-LISTP-1-IRREDUCIBLE-PP-MEMBER-UNIT-ASSOCIATE-PP))
   (8 4 (:REWRITE RIGHT-UNICITY-LAWS))
   (8 4 (:REWRITE PROJECTION-LAWS))
   (8 4 (:LINEAR SIZE->=-SIZE-1_E))
   (7 7 (:TYPE-PRESCRIPTION DIVIDES-PP))
   (7 3 (:REWRITE NULLITY-LAWS))
   (6 1 (:REWRITE CANCELLATION-LAWS-FOR-**_E))
   (4 4 (:REWRITE TRANSITIVITY-DIVIDES-PP))
   (4 4 (:REWRITE PRIME-PROPERTY-LEMMA))
   (4 4
      (:REWRITE ==_E-**_E-UNIT-ASSOCIATES-PP-WITNESS))
   (4 2 (:LINEAR SIZE-<-SIZE-**_E))
   (4 2 (:LINEAR SIZE-**_E))
   (2 2 (:REWRITE UNIT-ASSOCIATES-PP-SUFF)))
(UNIT-ASSOCIATES-PP-==_E-**_E-2
  (5109 4
        (:REWRITE IRREDUCIBLE-PP-UNIT-ASSOCIATES))
  (4384 226
        (:REWRITE IRREDUCIBLE-PP-IMPLIES-PRIME-PROPERTY))
  (3968 22 (:DEFINITION IRREDUCIBLE-PP))
  (2915 105 (:DEFINITION UNIT-PP))
  (2264 30 (:DEFINITION REDUCIBLE-PP))
  (1932 327 (:REWRITE UNIT-P-IMPLIES-EDP))
  (1724 113 (:REWRITE DIVIDES-PP-SUFF))
  (1587 49 (:DEFINITION UNIT-P))
  (1320 1320
        (:EQUIVALENCE ==_E-EQUIVALENCE-LAW))
  (1267 41 (:DEFINITION DIVIDES-P))
  (1239 460 (:REWRITE EQUIVALENCE-LAW))
  (1077 4 (:REWRITE DIVIDES-PP-**_E))
  (836 28 (:REWRITE REDUCIBLE-PP-**_E))
  (572 572 (:REWRITE CLOSURE-LAWS))
  (433 21 (:REWRITE ZERO-DIVISOR-LAW))
  (419 46
       (:REWRITE ASSOCIATIVITY-LAWS-FOR-++_E-&-**_E))
  (399 19 (:REWRITE UNIT-PP-CLOSURE-**_E))
  (370 113
       (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
  (360 156
       (:REWRITE INVERSE-CANCELLATION-LAWS-**_E))
  (350 22
       (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
  (327 327 (:TYPE-PRESCRIPTION UNIT-P))
  (327 327
       (:REWRITE MEMBER-UNIT-ASSOCIATE-PP-EDP-LISTP-IMPLIES-EDP))
  (284 105
       (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
  (279 49 (:REWRITE DIVIDES-P-SUFF))
  (226 226 (:TYPE-PRESCRIPTION IRREDUCIBLE-PP))
  (210 210
       (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
  (201 201 (:TYPE-PRESCRIPTION DIVIDES-PP))
  (188 22 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
  (159 159 (:TYPE-PRESCRIPTION UNIT-PP))
  (154 14 (:REWRITE REDUCIBLE-PP-**_E-1))
  (144 112 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
  (120 60 (:DEFINITION MV-NTH))
  (113 113 (:REWRITE TRANSITIVITY-DIVIDES-PP))
  (113 113 (:REWRITE PRIME-PROPERTY-LEMMA))
  (112 112 (:TYPE-PRESCRIPTION NATP-SIZE))
  (83 49
      (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
  (73 73
      (:REWRITE CLOSURE-LAWS-FOR-++_E-&-**_E))
  (63 21 (:REWRITE ZERO-DIVISOR-LAW-FOR-**_E))
  (51 39 (:REWRITE RIGHT-UNICITY-LAWS))
  (45 37 (:REWRITE NULLITY-LAWS))
  (32 32
      (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
  (30 30 (:REWRITE REDUCIBLE-PP-SUFF))
  (30 30 (:REWRITE DEFAULT-CDR))
  (30 30 (:REWRITE DEFAULT-CAR))
  (28 28 (:TYPE-PRESCRIPTION REDUCIBLE-PP))
  (28 14 (:REWRITE PROJECTION-LAWS))
  (24 12 (:LINEAR SIZE->=-SIZE-1_E))
  (22 22
      (:REWRITE IRREDUCIBLE-LISTP-1-IRREDUCIBLE-PP-MEMBER-UNIT-ASSOCIATE-PP))
  (18 3 (:REWRITE CANCELLATION-LAWS-FOR-**_E))
  (12 6 (:LINEAR SIZE-<-SIZE-**_E))
  (12 6 (:LINEAR SIZE-**_E))
  (4 4 (:REWRITE UNIT-ASSOCIATES-PP-SUFF)))
(UNIT-ASSOCIATES-PP-**_E-**_E-LST-DELETE-ONE-UNIT-ASSOCIATE-LEMMA
 (2608 432 (:REWRITE UNIT-P-IMPLIES-EDP))
 (2242 68 (:DEFINITION UNIT-P))
 (2184 7
       (:REWRITE IRREDUCIBLE-PP-UNIT-ASSOCIATES))
 (2004 54 (:DEFINITION DIVIDES-P))
 (1760 591 (:REWRITE EQUIVALENCE-LAW))
 (1602 14
       (:REWRITE IRREDUCIBLE-PP-IMPLIES-PRIME-PROPERTY))
 (1544 26 (:DEFINITION IRREDUCIBLE-PP))
 (1245 5 (:DEFINITION **_E-LST))
 (975 28 (:DEFINITION REDUCIBLE-PP))
 (939 3
      (:DEFINITION DELETE-ONE-UNIT-ASSOCIATE-PP))
 (635 25 (:REWRITE ZERO-DIVISOR-LAW))
 (507 499 (:REWRITE CLOSURE-LAWS))
 (432 432 (:TYPE-PRESCRIPTION UNIT-P))
 (378 12
      (:REWRITE INVERSE-CANCELLATION-LAWS-**_E))
 (334 28
      (:REWRITE IRREDUCIBLE-LISTP-1-IRREDUCIBLE-PP-MEMBER-UNIT-ASSOCIATE-PP))
 (326 2
      (:REWRITE DIVIDES-PP-MEMBER-UNIT-ASSOCIATE-PP-**_E-LST))
 (322 8 (:DEFINITION IRREDUCIBLE-LISTP-1))
 (288 2 (:REWRITE DIVIDES-PP-**_E))
 (270 270 (:TYPE-PRESCRIPTION UNIT-PP))
 (226 85
      (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
 (223 223 (:EQUIVALENCE ==_E-EQUIVALENCE-LAW))
 (210 28
      (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
 (194 68 (:REWRITE DIVIDES-P-SUFF))
 (170 170
      (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
 (163 2
      (:DEFINITION MEMBER-UNIT-ASSOCIATE-PP))
 (126 68
      (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
 (114 7 (:REWRITE DIVIDES-PP-SUFF))
 (112 56 (:DEFINITION MV-NTH))
 (111 35
      (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
 (98 4
     (:REWRITE UNIT-ASSOCIATES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP))
 (98 4
     (:REWRITE DIVIDES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP))
 (98 4
     (:REWRITE DIVIDES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-LEMMA))
 (90 16 (:REWRITE REDUCIBLE-PP-**_E))
 (72 72 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
 (72 72 (:TYPE-PRESCRIPTION NATP-SIZE))
 (65 7 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
 (57 57 (:REWRITE DEFAULT-CAR))
 (54 54 (:REWRITE DEFAULT-CDR))
 (46 46
     (:TYPE-PRESCRIPTION IRREDUCIBLE-LISTP-1))
 (42 26
     (:REWRITE CLOSURE-LAWS-FOR-++_E-&-**_E))
 (40 8 (:REWRITE REDUCIBLE-PP-**_E-LST))
 (36 36
     (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
 (32 32 (:TYPE-PRESCRIPTION IRREDUCIBLE-PP))
 (28 28 (:REWRITE REDUCIBLE-PP-SUFF))
 (26 26 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
 (20 6 (:REWRITE UNIT-PP-CLOSURE-**_E))
 (18 8 (:REWRITE REDUCIBLE-PP-**_E-1))
 (16 8 (:LINEAR SIZE->=-SIZE-1_E))
 (15 15 (:TYPE-PRESCRIPTION DIVIDES-PP))
 (11 4 (:REWRITE RIGHT-UNICITY-LAWS))
 (7 7 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
 (7 7 (:REWRITE TRANSITIVITY-DIVIDES-PP))
 (7 7 (:REWRITE PRIME-PROPERTY-LEMMA))
 (7 1 (:REWRITE PROJECTION-LAWS))
 (6 3 (:REWRITE NULLITY-LAWS))
 (4 4 (:TYPE-PRESCRIPTION REDUCIBLE-PP))
 (4
   4
   (:REWRITE UNIT-ASSOCIATES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP-1))
 (4 4
    (:REWRITE **_E-IRREDUCIBLE-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP))
 (2 2 (:REWRITE ZERO-DIVISOR-LAW-FOR-**_E))
 (2
  2
  (:REWRITE
       **_E-IRREDUCIBLE-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP-LEMMA)))
(UNIT-ASSOCIATES-PP-**_E-**_E-LST-DELETE-ONE-UNIT-ASSOCIATE
 (39527 987 (:DEFINITION UNIT-P))
 (39194 15211 (:REWRITE EQUIVALENCE-LAW))
 (32908 20 (:DEFINITION IRREDUCIBLE-P))
 (30272 762 (:DEFINITION DIVIDES-P))
 (27410 6672 (:REWRITE UNIT-P-IMPLIES-EDP))
 (18089 20 (:DEFINITION REDUCIBLE-P))
 (13762 136 (:DEFINITION IRREDUCIBLE-PP))
 (11123 685 (:REWRITE ZERO-DIVISOR-LAW))
 (11060 11044 (:REWRITE CLOSURE-LAWS))
 (9304 990 (:REWRITE DIVIDES-P-SUFF))
 (9215 24
       (:REWRITE IRREDUCIBLE-PP-UNIT-ASSOCIATES))
 (9039 20 (:REWRITE REDUCIBLE-P-SUFF))
 (8572 160 (:DEFINITION REDUCIBLE-PP))
 (7160 52
       (:REWRITE IRREDUCIBLE-PP-IMPLIES-PRIME-PROPERTY))
 (6933 6933 (:TYPE-PRESCRIPTION UNIT-P))
 (6785 48 (:DEFINITION IRREDUCIBLE-LISTP-1))
 (5039 37
       (:REWRITE IRREDUCIBLE-LISTP-1-IMPLIES-EDP-LISTP))
 (3154 987
       (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
 (1952
      136
      (:REWRITE IRREDUCIBLE-LISTP-1-IRREDUCIBLE-PP-MEMBER-UNIT-ASSOCIATE-PP))
 (1811
     16
     (:REWRITE UNIT-ASSOCIATES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP))
 (1811 16
       (:REWRITE DIVIDES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP))
 (1811 16
       (:REWRITE DIVIDES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-LEMMA))
 (1787 1787 (:TYPE-PRESCRIPTION UNIT-PP))
 (1419 544
       (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
 (1271 1271
       (:EQUIVALENCE ==_E-EQUIVALENCE-LAW))
 (1242 136
       (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
 (1088 1088
       (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
 (910 455 (:DEFINITION MV-NTH))
 (880 72 (:REWRITE REDUCIBLE-PP-**_E))
 (848 6 (:REWRITE DIVIDES-PP-**_E))
 (740 26 (:REWRITE DIVIDES-PP-SUFF))
 (706 6
      (:REWRITE DIVIDES-PP-MEMBER-UNIT-ASSOCIATE-PP-**_E-LST))
 (701 701 (:REWRITE DEFAULT-CAR))
 (616 616
      (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
 (391 391 (:REWRITE DEFAULT-CDR))
 (320 26 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
 (264 12
      (:REWRITE ASSOCIATIVITY-LAWS-FOR-++_E-&-**_E))
 (246 126
      (:REWRITE CLOSURE-LAWS-FOR-++_E-&-**_E))
 (245 209 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
 (227 227
      (:TYPE-PRESCRIPTION IRREDUCIBLE-LISTP-1))
 (220 20
      (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-P))
 (209 209 (:TYPE-PRESCRIPTION NATP-SIZE))
 (174 166
      (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
 (160 160 (:REWRITE REDUCIBLE-PP-SUFF))
 (156 36 (:REWRITE REDUCIBLE-PP-**_E-1))
 (140 38 (:REWRITE UNIT-PP-CLOSURE-**_E))
 (136 136 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
 (100 100 (:TYPE-PRESCRIPTION IRREDUCIBLE-PP))
 (88 12
     (:REWRITE INVERSE-CANCELLATION-LAWS-**_E))
 (78 22 (:REWRITE RIGHT-UNICITY-LAWS))
 (62 19 (:REWRITE NULLITY-LAWS))
 (60 8 (:REWRITE ZERO-DIVISOR-LAW-FOR-**_E))
 (56 56 (:REWRITE RIGHT-UNICITY-LAW-FOR-*_E))
 (56 56 (:REWRITE LEFT-UNICITY-LAWS))
 (51 51 (:TYPE-PRESCRIPTION DIVIDES-PP))
 (49 23 (:LINEAR SIZE->=-SIZE-1_E))
 (41 5 (:REWRITE CANCELLATION-LAWS-FOR-**_E))
 (32 32 (:TYPE-PRESCRIPTION REDUCIBLE-PP))
 (26 26 (:REWRITE TRANSITIVITY-DIVIDES-PP))
 (26 26 (:REWRITE PRIME-PROPERTY-LEMMA))
 (24 24 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
 (24 12 (:REWRITE REDUCIBLE-PP-**_E-LST))
 (20 20 (:REWRITE REDUCIBLE-P-SUFF-2))
 (20 5 (:REWRITE PROJECTION-LAWS))
 (16
   16
   (:REWRITE UNIT-ASSOCIATES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP-1))
 (16
    16
    (:REWRITE **_E-IRREDUCIBLE-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP))
 (6
  6
  (:REWRITE
       **_E-IRREDUCIBLE-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP-LEMMA)))
(UNIT-ASSOCIATES-PP-**_E-CANCELLATION
  (9716 1415 (:REWRITE UNIT-P-IMPLIES-EDP))
  (8686 182 (:DEFINITION UNIT-P))
  (7294 2484 (:REWRITE EQUIVALENCE-LAW))
  (6707 142 (:DEFINITION DIVIDES-P))
  (3956 59
        (:REWRITE IRREDUCIBLE-PP-UNIT-ASSOCIATES))
  (3321 31 (:DEFINITION IRREDUCIBLE-PP))
  (2598 74
        (:REWRITE IRREDUCIBLE-PP-IMPLIES-PRIME-PROPERTY))
  (2286 104 (:REWRITE ZERO-DIVISOR-LAW))
  (2055 2007 (:REWRITE CLOSURE-LAWS))
  (1861 47 (:DEFINITION REDUCIBLE-PP))
  (1858 182 (:REWRITE DIVIDES-P-SUFF))
  (1660 328
        (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
  (1417 1417
        (:REWRITE MEMBER-UNIT-ASSOCIATE-PP-EDP-LISTP-IMPLIES-EDP))
  (1415 1415 (:TYPE-PRESCRIPTION UNIT-P))
  (1375 164
        (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
  (1335 234
        (:REWRITE INVERSE-CANCELLATION-LAWS-**_E))
  (1215 48 (:REWRITE DIVIDES-PP-**_E))
  (875 37 (:REWRITE DIVIDES-PP-SUFF))
  (640 48 (:REWRITE REDUCIBLE-PP-**_E))
  (552 182
       (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
  (489 33
       (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
  (447 39
       (:REWRITE ASSOCIATIVITY-LAWS-FOR-++_E-&-**_E))
  (264 227 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
  (188 94 (:DEFINITION MV-NTH))
  (185 47 (:REWRITE REDUCIBLE-PP-SUFF))
  (183 183 (:TYPE-PRESCRIPTION NATP-SIZE))
  (158 37 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
  (152 24 (:REWRITE UNIT-PP-CLOSURE-**_E))
  (152 24 (:REWRITE REDUCIBLE-PP-**_E-1))
  (144 144 (:TYPE-PRESCRIPTION DIVIDES-PP))
  (118 118
       (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
  (102 102 (:TYPE-PRESCRIPTION IRREDUCIBLE-PP))
  (69 23 (:LINEAR SIZE->=-SIZE-1_E))
  (59 59 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
  (57 19 (:REWRITE ZERO-DIVISOR-LAW-FOR-**_E))
  (48 48 (:TYPE-PRESCRIPTION REDUCIBLE-PP))
  (47 47 (:REWRITE DEFAULT-CDR))
  (47 47 (:REWRITE DEFAULT-CAR))
  (37 37 (:REWRITE TRANSITIVITY-DIVIDES-PP))
  (37 37 (:REWRITE PRIME-PROPERTY-LEMMA))
  (33 33
      (:REWRITE IRREDUCIBLE-LISTP-1-IRREDUCIBLE-PP-MEMBER-UNIT-ASSOCIATE-PP))
  (31 31 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
  (28 8 (:LINEAR SIZE-<-SIZE-**_E))
  (27 15 (:REWRITE PROJECTION-LAWS))
  (24 12 (:REWRITE RIGHT-UNICITY-LAWS))
  (24 12 (:REWRITE NULLITY-LAWS))
  (18 8 (:LINEAR SIZE-**_E)))
(UNIT-ASSOCIATES-PP-**_E-**_E-LST-DELETE-ONE-UNIT-ASSOCIATE-PP-CANCELLATION
 (2444 71 (:DEFINITION UNIT-P))
 (2315 357 (:REWRITE UNIT-P-IMPLIES-EDP))
 (2131 51 (:DEFINITION DIVIDES-P))
 (1954 744 (:REWRITE EQUIVALENCE-LAW))
 (1274 6 (:DEFINITION **_E-LST))
 (1147 7
       (:REWRITE IRREDUCIBLE-PP-UNIT-ASSOCIATES))
 (699 32 (:REWRITE ZERO-DIVISOR-LAW))
 (686 2
      (:REWRITE IRREDUCIBLE-LISTP-IMPLIES-EDP-LISTP))
 (680 2 (:DEFINITION IRREDUCIBLE-LISTP))
 (663 2 (:DEFINITION IRREDUCIBLE-P))
 (625 625 (:REWRITE CLOSURE-LAWS))
 (542 8
      (:REWRITE IRREDUCIBLE-PP-IMPLIES-PRIME-PROPERTY))
 (390 390 (:TYPE-PRESCRIPTION UNIT-P))
 (365 2
      (:REWRITE DIVIDES-PP-MEMBER-UNIT-ASSOCIATE-PP-**_E-LST))
 (357 357
      (:REWRITE MEMBER-UNIT-ASSOCIATE-PP-EDP-LISTP-IMPLIES-EDP))
 (340 2
      (:DEFINITION DELETE-ONE-UNIT-ASSOCIATE-PP))
 (298 26
      (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
 (288 71 (:REWRITE DIVIDES-P-SUFF))
 (277 2 (:DEFINITION REDUCIBLE-P))
 (275 2 (:REWRITE REDUCIBLE-P-SUFF))
 (187
     5
     (:REWRITE UNIT-ASSOCIATES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP))
 (182 177 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
 (142 25
      (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
 (139 2
      (:DEFINITION MEMBER-UNIT-ASSOCIATE-PP))
 (118 71
      (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
 (111 111 (:TYPE-PRESCRIPTION NATP-SIZE))
 (102 4 (:REWRITE DIVIDES-PP-SUFF))
 (78 4
     (:REWRITE DIVIDES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP))
 (78 4
     (:REWRITE DIVIDES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-LEMMA))
 (72 4 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
 (71 23 (:LINEAR SIZE->=-SIZE-1_E))
 (53 17 (:REWRITE REDUCIBLE-PP-**_E-LST))
 (50 50
     (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
 (40 40
     (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
 (26 26
     (:REWRITE IRREDUCIBLE-LISTP-1-IRREDUCIBLE-PP-MEMBER-UNIT-ASSOCIATE-PP))
 (24 24 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
 (24 24 (:REWRITE REDUCIBLE-PP-SUFF))
 (24 24 (:REWRITE DEFAULT-CAR))
 (22 2 (:DEFINITION IRREDUCIBLE-LISTP-1))
 (18 18 (:REWRITE DEFAULT-CDR))
 (12 4 (:REWRITE RIGHT-UNICITY-LAWS))
 (10 10
     (:TYPE-PRESCRIPTION IRREDUCIBLE-LISTP))
 (10 10 (:TYPE-PRESCRIPTION DIVIDES-PP))
 (10 2
     (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
 (8 4 (:DEFINITION MV-NTH))
 (7 7 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
 (7 3 (:REWRITE NULLITY-LAWS))
 (7 1 (:REWRITE PROJECTION-LAWS))
 (5
   5
   (:REWRITE UNIT-ASSOCIATES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP-1))
 (5 2 (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-P))
 (4 4 (:REWRITE TRANSITIVITY-DIVIDES-PP))
 (4 4 (:REWRITE PRIME-PROPERTY-LEMMA))
 (4 2
    (:REWRITE IRREDUCIBLE-LISTP-1-DELETE-ONE-UNIT-ASSOCIATE-PP))
 (3
   3
   (:REWRITE
        **_E-IRREDUCIBLE-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP-LEMMA))
 (2 2 (:REWRITE REDUCIBLE-P-SUFF-2)))
(IRREDUCIBLE-FACTORIZATION-UNIQUENESS-GENERAL-1
 (7579 1235 (:REWRITE UNIT-P-IMPLIES-EDP))
 (7258 206 (:DEFINITION UNIT-P))
 (6612 160 (:DEFINITION DIVIDES-P))
 (5771 2052 (:REWRITE EQUIVALENCE-LAW))
 (3869 25
       (:REWRITE IRREDUCIBLE-PP-UNIT-ASSOCIATES))
 (2139 91 (:REWRITE ZERO-DIVISOR-LAW))
 (1842 1842 (:REWRITE CLOSURE-LAWS))
 (1582 7
       (:REWRITE DIVIDES-PP-MEMBER-UNIT-ASSOCIATE-PP-**_E-LST))
 (1352 1352 (:TYPE-PRESCRIPTION UNIT-P))
 (1329 9
       (:REWRITE IRREDUCIBLE-LISTP-IMPLIES-EDP-LISTP))
 (1302 9 (:DEFINITION IRREDUCIBLE-LISTP))
 (1296 34
       (:REWRITE IRREDUCIBLE-PP-IMPLIES-PRIME-PROPERTY))
 (1236 9 (:DEFINITION IRREDUCIBLE-P))
 (1235 1235
       (:REWRITE MEMBER-UNIT-ASSOCIATE-PP-EDP-LISTP-IMPLIES-EDP))
 (884
     20
     (:REWRITE UNIT-ASSOCIATES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP))
 (817 100
      (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
 (564 9 (:DEFINITION REDUCIBLE-P))
 (554 206 (:REWRITE DIVIDES-P-SUFF))
 (470 16 (:REWRITE DIVIDES-PP-SUFF))
 (470 4
      (:DEFINITION DELETE-ONE-UNIT-ASSOCIATE-PP))
 (428 9 (:REWRITE REDUCIBLE-P-SUFF))
 (422 18
      (:REWRITE DIVIDES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP))
 (422 18
      (:REWRITE DIVIDES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-LEMMA))
 (331 106
      (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
 (330 206
      (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
 (268 268 (:EQUIVALENCE ==_E-EQUIVALENCE-LAW))
 (236 17 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
 (212 212
      (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
 (188 153 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
 (166 6
      (:REWRITE ASSOCIATIVITY-LAWS-FOR-++_E-&-**_E))
 (153 153 (:TYPE-PRESCRIPTION NATP-SIZE))
 (145 1 (:DEFINITION EDP-LISTP))
 (129 129 (:REWRITE EDP-**_E-LST))
 (108 108
      (:REWRITE IRREDUCIBLE-LISTP-1-IRREDUCIBLE-PP-MEMBER-UNIT-ASSOCIATE-PP))
 (104 104 (:REWRITE REDUCIBLE-PP-SUFF))
 (100 100 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
 (94 94 (:REWRITE DEFAULT-CAR))
 (92 92
     (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
 (88 12
     (:REWRITE INVERSE-CANCELLATION-LAWS-**_E))
 (76 32 (:REWRITE REDUCIBLE-PP-**_E))
 (72 40
     (:REWRITE CLOSURE-LAWS-FOR-++_E-&-**_E))
 (59 59 (:REWRITE DEFAULT-CDR))
 (52 16 (:REWRITE REDUCIBLE-PP-**_E-1))
 (45 45
     (:TYPE-PRESCRIPTION IRREDUCIBLE-LISTP))
 (41 9 (:REWRITE RIGHT-UNICITY-LAWS))
 (40 40 (:TYPE-PRESCRIPTION DIVIDES-PP))
 (39 17 (:LINEAR SIZE->=-SIZE-1_E))
 (38 10 (:REWRITE NULLITY-LAWS))
 (36 32 (:REWRITE REDUCIBLE-PP-**_E-LST))
 (36 18 (:DEFINITION MV-NTH))
 (25 25 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
 (19 7
     (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
 (18 1 (:REWRITE LEAST-DIVIDES-PP=1_E))
 (17 17 (:REWRITE TRANSITIVITY-DIVIDES-PP))
 (17 17 (:REWRITE PRIME-PROPERTY-LEMMA))
 (16 16 (:REWRITE UNIT-PP-CLOSURE-**_E))
 (14 2 (:REWRITE ZERO-DIVISOR-LAW-FOR-**_E))
 (12 9 (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-P))
 (9 9 (:REWRITE REDUCIBLE-P-SUFF-2))
 (9
   9
   (:REWRITE
        **_E-IRREDUCIBLE-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP-LEMMA))
 (8 8 (:REWRITE NOT-IRREDUCIBLE-PP-1_E))
 (7 1 (:REWRITE PROJECTION-LAWS))
 (2 2 (:REWRITE |1_E-0_E|))
 (2 1
    (:REWRITE IRREDUCIBLE-LISTP-1-DELETE-ONE-UNIT-ASSOCIATE-PP))
 (1 1 (:REWRITE UNIT-PP-1_E)))
(IRREDUCIBLE-LISTP-=-IRREDUCIBLE-LISTP-1
  (23529 6900 (:REWRITE EQUIVALENCE-LAW))
  (22313 435 (:DEFINITION UNIT-P))
  (21909 2 (:DEFINITION IRREDUCIBLE-P))
  (16419 329 (:DEFINITION DIVIDES-P))
  (14496 2 (:DEFINITION REDUCIBLE-P))
  (14076 3155 (:REWRITE UNIT-P-IMPLIES-EDP))
  (8985 265 (:REWRITE ZERO-DIVISOR-LAW))
  (7727 435 (:REWRITE DIVIDES-P-SUFF))
  (6614 6494 (:REWRITE CLOSURE-LAWS))
  (4594 10 (:DEFINITION IRREDUCIBLE-PP))
  (3738 2 (:REWRITE REDUCIBLE-P-SUFF))
  (3468 10 (:DEFINITION REDUCIBLE-PP))
  (3175 3175 (:TYPE-PRESCRIPTION UNIT-P))
  (3155 3155
        (:REWRITE MEMBER-UNIT-ASSOCIATE-PP-EDP-LISTP-IMPLIES-EDP))
  (3018 38 (:DEFINITION UNIT-PP))
  (2858 76
        (:REWRITE IRREDUCIBLE-PP-IMPLIES-PRIME-PROPERTY))
  (1253 435
        (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
  (674 10 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
  (644 24
       (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
  (618 38 (:REWRITE DIVIDES-PP-SUFF))
  (304 224 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
  (224 7 (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-P))
  (204 31 (:LINEAR SIZE->=-SIZE-1_E))
  (196 196
       (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
  (189 189 (:TYPE-PRESCRIPTION NATP-SIZE))
  (114 38
       (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
  (114 38 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
  (86 86 (:TYPE-PRESCRIPTION DIVIDES-PP))
  (76 76
      (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
  (66 66
      (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
  (62 28 (:DEFINITION MV-NTH))
  (38 38 (:REWRITE TRANSITIVITY-DIVIDES-PP))
  (38 38 (:REWRITE RIGHT-UNICITY-LAWS))
  (38 38 (:REWRITE PRIME-PROPERTY-LEMMA))
  (38 38 (:REWRITE NULLITY-LAWS))
  (38 14 (:REWRITE RIGHT-UNICITY-LAW-FOR-*_E))
  (32 32 (:REWRITE DEFAULT-CAR))
  (24 24
      (:REWRITE IRREDUCIBLE-LISTP-1-IRREDUCIBLE-PP-MEMBER-UNIT-ASSOCIATE-PP))
  (20 20 (:REWRITE DEFAULT-CDR))
  (10 10 (:REWRITE REDUCIBLE-PP-SUFF))
  (5 5 (:REWRITE |1_E-0_E|))
  (2 2 (:REWRITE REDUCIBLE-P-SUFF-2)))
(IRREDUCIBLE-FACTORIZATION-UNIQUENESS-GENERAL
 (45908 13340 (:REWRITE EQUIVALENCE-LAW))
 (27752 6232 (:REWRITE UNIT-P-IMPLIES-EDP))
 (18066 540 (:REWRITE ZERO-DIVISOR-LAW))
 (15484 922 (:REWRITE DIVIDES-P-SUFF))
 (13292 13052 (:REWRITE CLOSURE-LAWS))
 (7284 4 (:REWRITE REDUCIBLE-P-SUFF))
 (6272 6272 (:TYPE-PRESCRIPTION UNIT-P))
 (6252 6236
       (:REWRITE MEMBER-UNIT-ASSOCIATE-PP-EDP-LISTP-IMPLIES-EDP))
 (3996 322
       (:REWRITE IRREDUCIBLE-PP-IMPLIES-PRIME-PROPERTY))
 (3329 5
       (:DEFINITION MEMBER-UNIT-ASSOCIATE-PP))
 (3146 10
       (:REWRITE IRREDUCIBLE-PP-UNIT-ASSOCIATES))
 (2624 922
       (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
 (2094 106
       (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
 (1922 1922
       (:EQUIVALENCE ==_E-EQUIVALENCE-LAW))
 (1861 161 (:REWRITE DIVIDES-PP-SUFF))
 (1668
     10
     (:REWRITE UNIT-ASSOCIATES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP))
 (1668 10
       (:REWRITE DIVIDES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP))
 (1668 10
       (:REWRITE DIVIDES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-LEMMA))
 (1423 4
       (:REWRITE IRREDUCIBLE-FACTORIZATION-UNIQUENESS-GENERAL-1))
 (1140 42 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
 (1122 3
       (:REWRITE DIVIDES-PP-MEMBER-UNIT-ASSOCIATE-PP-**_E-LST))
 (968 6 (:DEFINITION **_E-LST))
 (888 584 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
 (864 864
      (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
 (584 584 (:TYPE-PRESCRIPTION NATP-SIZE))
 (501 161
      (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
 (480 480 (:TYPE-PRESCRIPTION IRREDUCIBLE-PP))
 (410 154
      (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
 (308 308
      (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
 (164 64 (:LINEAR SIZE->=-SIZE-1_E))
 (161 161 (:REWRITE TRANSITIVITY-DIVIDES-PP))
 (161 161 (:REWRITE PRIME-PROPERTY-LEMMA))
 (125 109 (:REWRITE RIGHT-UNICITY-LAWS))
 (125 109 (:REWRITE NULLITY-LAWS))
 (110 110
      (:REWRITE IRREDUCIBLE-LISTP-1-IRREDUCIBLE-PP-MEMBER-UNIT-ASSOCIATE-PP))
 (106 2
      (:DEFINITION DELETE-ONE-UNIT-ASSOCIATE-PP))
 (104 104 (:REWRITE DEFAULT-CAR))
 (90 90 (:TYPE-PRESCRIPTION UNIT-PP))
 (87 87 (:REWRITE DEFAULT-CDR))
 (80 4 (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-P))
 (76 28 (:REWRITE RIGHT-UNICITY-LAW-FOR-*_E))
 (52 52 (:REWRITE EDP-**_E-LST))
 (42 42 (:REWRITE REDUCIBLE-PP-SUFF))
 (18 18 (:REWRITE REDUCIBLE-PP-**_E-LST))
 (15 15 (:TYPE-PRESCRIPTION EDP-LISTP))
 (10 10 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
 (10
   10
   (:REWRITE UNIT-ASSOCIATES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP-1))
 (10
    10
    (:REWRITE **_E-IRREDUCIBLE-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP))
 (7 7
    (:REWRITE IRREDUCIBLE-LISTP-IMPLIES-EDP-LISTP))
 (7 1
    (:DEFINITION DELETE-ONE-UNIT-ASSOCIATE))
 (5 1 (:DEFINITION MEMBER-UNIT-ASSOCIATE))
 (4 4 (:REWRITE REDUCIBLE-P-SUFF-2))
 (4 4 (:REWRITE PROJECTION-LAWS))
 (3 3 (:REWRITE UNIT-ASSOCIATES-P-SUFF))
 (3
  3
  (:REWRITE
       **_E-IRREDUCIBLE-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP-LEMMA)))
(IRREDUCIBLE-FACTORIZATION-UNIQUENESS-1
 (564 78 (:REWRITE UNIT-P-IMPLIES-EDP))
 (530 10 (:DEFINITION UNIT-P))
 (506 6 (:DEFINITION DIVIDES-P))
 (464 148 (:REWRITE EQUIVALENCE-LAW))
 (178 8 (:REWRITE ZERO-DIVISOR-LAW))
 (140 140 (:REWRITE CLOSURE-LAWS))
 (78 78 (:TYPE-PRESCRIPTION UNIT-P))
 (78 78
     (:REWRITE MEMBER-UNIT-ASSOCIATE-PP-EDP-LISTP-IMPLIES-EDP))
 (72 2
     (:REWRITE IRREDUCIBLE-PP-UNIT-ASSOCIATES))
 (50 2 (:DEFINITION IRREDUCIBLE-LISTP-1))
 (42 4
     (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
 (32 1
     (:REWRITE DIVIDES-PP-MEMBER-UNIT-ASSOCIATE-PP-**_E-LST))
 (22 10
     (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
 (22 10 (:REWRITE DIVIDES-P-SUFF))
 (17 1 (:REWRITE DIVIDES-PP-SUFF))
 (17 1
     (:DEFINITION MEMBER-UNIT-ASSOCIATE-PP))
 (12 12 (:TYPE-PRESCRIPTION IRREDUCIBLE-PP))
 (11 11 (:REWRITE DEFAULT-CAR))
 (10 2
     (:REWRITE IRREDUCIBLE-PP-IMPLIES-PRIME-PROPERTY))
 (8 8
    (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
 (7 7 (:REWRITE DEFAULT-CDR))
 (7 1 (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
 (5 5
    (:TYPE-PRESCRIPTION MEMBER-UNIT-ASSOCIATE-PP))
 (4 4
    (:REWRITE IRREDUCIBLE-LISTP-1-IRREDUCIBLE-PP-MEMBER-UNIT-ASSOCIATE-PP))
 (4 2
    (:REWRITE UNIT-ASSOCIATES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP))
 (4 2
    (:REWRITE DIVIDES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP))
 (4 2
    (:REWRITE DIVIDES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-LEMMA))
 (3 3 (:TYPE-PRESCRIPTION DIVIDES-PP))
 (2 2 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
 (2
   2
   (:REWRITE UNIT-ASSOCIATES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP-1))
 (2 2 (:REWRITE PROJECTION-LAWS))
 (2 2 (:REWRITE EDP-**_E-LST))
 (2 2
    (:REWRITE COMMUTATIVITY-LAWS-FOR-++_E-&-**_E))
 (2 2
    (:REWRITE **_E-IRREDUCIBLE-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP))
 (2 1
    (:REWRITE IRREDUCIBLE-LISTP-IMPLIES-EDP-LISTP))
 (1 1
    (:TYPE-PRESCRIPTION IRREDUCIBLE-LISTP))
 (1 1 (:TYPE-PRESCRIPTION EDP-LISTP))
 (1 1 (:REWRITE TRANSITIVITY-DIVIDES-PP))
 (1 1 (:REWRITE RIGHT-UNICITY-LAWS))
 (1 1 (:REWRITE PRIME-PROPERTY-LEMMA))
 (1 1 (:REWRITE NULLITY-LAWS))
 (1 1
    (:REWRITE IRREDUCIBLE-LISTP-1-IMPLIES-EDP-LISTP))
 (1
  1
  (:REWRITE
       **_E-IRREDUCIBLE-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP-LEMMA)))
(IRREDUCIBLE-FACTORIZATION-UNIQUENESS
 (48180 14082 (:REWRITE EQUIVALENCE-LAW))
 (28725 6491 (:REWRITE UNIT-P-IMPLIES-EDP))
 (18616 574 (:REWRITE ZERO-DIVISOR-LAW))
 (16044 963 (:REWRITE DIVIDES-P-SUFF))
 (13819 13579 (:REWRITE CLOSURE-LAWS))
 (7776 5 (:REWRITE REDUCIBLE-P-SUFF))
 (6541 6541 (:TYPE-PRESCRIPTION UNIT-P))
 (6511 6495
       (:REWRITE MEMBER-UNIT-ASSOCIATE-PP-EDP-LISTP-IMPLIES-EDP))
 (3224 228
       (:REWRITE IRREDUCIBLE-PP-IMPLIES-PRIME-PROPERTY))
 (2808 4
       (:DEFINITION MEMBER-UNIT-ASSOCIATE-PP))
 (2793 963
       (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-P))
 (2300 2
       (:REWRITE IRREDUCIBLE-FACTORIZATION-UNIQUENESS-GENERAL))
 (1984 92
       (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-PP))
 (1784 4
       (:REWRITE IRREDUCIBLE-FACTORIZATION-UNIQUENESS-GENERAL-1))
 (1482 114 (:REWRITE DIVIDES-PP-SUFF))
 (1364 8
       (:REWRITE IRREDUCIBLE-PP-UNIT-ASSOCIATES))
 (1320
     8
     (:REWRITE UNIT-ASSOCIATES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP))
 (1320 8
       (:REWRITE DIVIDES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP))
 (1320 8
       (:REWRITE DIVIDES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-LEMMA))
 (1088 8 (:DEFINITION **_E-LST))
 (1060 28 (:REWRITE UNIT-PP-NOT-REDUCIBLE-PP))
 (892 892
      (:TYPE-PRESCRIPTION BOOLEANP-DIVIDES-P))
 (852 548 (:TYPE-PRESCRIPTION NATP-SIZE-==_E))
 (548 548 (:TYPE-PRESCRIPTION NATP-SIZE))
 (380 380 (:TYPE-PRESCRIPTION IRREDUCIBLE-PP))
 (362 114
      (:REWRITE RR_E=0-IMPLIES-DIVIDES-PP))
 (304 108
      (:REWRITE SIZE=SIZE-1_E-IMPLIES-UNIT-PP))
 (216 216
      (:REWRITE IRREDUCIBLE-PP-IMPLIES-UNIT-PP-FACTOR))
 (156 60 (:LINEAR SIZE->=-SIZE-1_E))
 (114 114 (:REWRITE TRANSITIVITY-DIVIDES-PP))
 (114 114 (:REWRITE PRIME-PROPERTY-LEMMA))
 (106 2
      (:DEFINITION DELETE-ONE-UNIT-ASSOCIATE-PP))
 (104 96 (:REWRITE RIGHT-UNICITY-LAWS))
 (104 96 (:REWRITE NULLITY-LAWS))
 (99 99 (:REWRITE DEFAULT-CAR))
 (96 96
     (:REWRITE IRREDUCIBLE-LISTP-1-IRREDUCIBLE-PP-MEMBER-UNIT-ASSOCIATE-PP))
 (96 5 (:REWRITE SIZE-IMPLIES-IRREDUCIBLE-P))
 (80 32 (:REWRITE RIGHT-UNICITY-LAW-FOR-*_E))
 (78 78 (:REWRITE DEFAULT-CDR))
 (60 2
     (:REWRITE DIVIDES-PP-MEMBER-UNIT-ASSOCIATE-PP-**_E-LST))
 (44 44 (:TYPE-PRESCRIPTION UNIT-PP))
 (36 36 (:REWRITE EDP-**_E-LST))
 (28 28 (:REWRITE REDUCIBLE-PP-SUFF))
 (14 14 (:TYPE-PRESCRIPTION EDP-LISTP))
 (8 8 (:REWRITE UNIT-ASSOCIATES-PP-SUFF))
 (8
   8
   (:REWRITE UNIT-ASSOCIATES-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP-1))
 (8 8
    (:REWRITE **_E-IRREDUCIBLE-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP))
 (7 1
    (:DEFINITION DELETE-ONE-UNIT-ASSOCIATE))
 (6 6
    (:REWRITE IRREDUCIBLE-LISTP-IMPLIES-EDP-LISTP))
 (5 5 (:REWRITE REDUCIBLE-P-SUFF-2))
 (5 1 (:DEFINITION MEMBER-UNIT-ASSOCIATE))
 (4 4
    (:TYPE-PRESCRIPTION UNIT-ASSOCIATES-PP))
 (4 4
    (:TYPE-PRESCRIPTION BOOLEANP-UNIT-ASSOCIATES-P))
 (4 4 (:REWRITE REDUCIBLE-PP-**_E-LST))
 (4 4 (:REWRITE LEFT-UNICITY-LAWS))
 (3 3 (:REWRITE UNIT-ASSOCIATES-P-SUFF))
 (2
  2
  (:REWRITE
       **_E-IRREDUCIBLE-PP-**_E-LST-IMPLIES-MEMBER-UNIT-ASSOCIATE-PP-LEMMA)))
