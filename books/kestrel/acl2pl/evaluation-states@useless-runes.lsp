(ACL2PL::BINDINGP)
(ACL2PL::BOOLEANP-OFBINDINGP)
(ACL2PL::MAPP-WHEN-BINDINGP
 (161 50 (:REWRITE <<-TRICHOTOMY))
 (143 29 (:REWRITE <<-ASYMMETRIC))
 (133 133 (:REWRITE DEFAULT-CAR))
 (77 77 (:REWRITE DEFAULT-CDR))
 (77 77
     (:REWRITE CAR-OF-TRUE-LIST-LIST-FIX-X-NORMALIZE-CONST-UNDER-LIST-EQUIV))
 (59 47 (:REWRITE <<-TRANSITIVE))
 (54 21
     (:REWRITE ACL2PL::SYMBOL-VALUEP-OF-CAR-WHEN-SYMBOL-VALUE-LISTP))
 (28 28
     (:REWRITE ACL2PL::SYMBOL-VALUEP-WHEN-IN-SYMBOL-VALUE-SETP-BINDS-FREE-X))
 (24
  24
  (:REWRITE
     CDR-OF-TRUE-LIST-LIST-FIX-X-NORMALIZE-CONST-UNDER-TRUE-LIST-LIST-EQUIV))
 (18 6 (:REWRITE OMAP::MAPP-WHEN-NOT-EMPTY))
 (12 12 (:TYPE-PRESCRIPTION OMAP::EMPTY))
 (11 11
     (:REWRITE ACL2PL::SYMBOL-VALUE-LISTP-WHEN-NOT-CONSP))
 (3 3 (:REWRITE <<-IRREFLEXIVE)))
(ACL2PL::BINDINGP-OF-TAIL
 (57 15 (:REWRITE <<-TRICHOTOMY))
 (51 9 (:REWRITE <<-ASYMMETRIC))
 (39 6
     (:REWRITE ACL2PL::SYMBOL-VALUEP-WHEN-MAYBE-SYMBOL-VALUEP))
 (30 3
     (:REWRITE ACL2PL::MAYBE-SYMBOL-VALUEP-WHEN-SYMBOL-VALUEP))
 (27 27 (:REWRITE DEFAULT-CAR))
 (24 6
     (:REWRITE ACL2PL::VALUEP-WHEN-MAYBE-VALUEP))
 (22 22 (:TYPE-PRESCRIPTION OMAP::MFIX))
 (20 20 (:REWRITE DEFAULT-CDR))
 (15 15
     (:REWRITE CAR-OF-TRUE-LIST-LIST-FIX-X-NORMALIZE-CONST-UNDER-LIST-EQUIV))
 (15 15 (:REWRITE <<-TRANSITIVE))
 (15 6
     (:REWRITE ACL2PL::SYMBOL-VALUEP-OF-CAR-WHEN-SYMBOL-VALUE-LISTP))
 (15 3
     (:REWRITE ACL2PL::MAYBE-VALUEP-WHEN-VALUEP))
 (9 9
    (:TYPE-PRESCRIPTION ACL2PL::MAYBE-VALUEP))
 (9 9
    (:TYPE-PRESCRIPTION ACL2PL::MAYBE-SYMBOL-VALUEP))
 (6 6 (:TYPE-PRESCRIPTION ACL2PL::VALUEP))
 (6 6
    (:TYPE-PRESCRIPTION ACL2PL::SYMBOL-VALUEP))
 (6 6
    (:REWRITE ACL2PL::SYMBOL-VALUEP-WHEN-IN-SYMBOL-VALUE-SETP-BINDS-FREE-X))
 (6
  6
  (:REWRITE
     CDR-OF-TRUE-LIST-LIST-FIX-X-NORMALIZE-CONST-UNDER-TRUE-LIST-LIST-EQUIV))
 (3 3
    (:REWRITE ACL2PL::SYMBOL-VALUE-LISTP-WHEN-NOT-CONSP))
 (3 1 (:REWRITE OMAP::MFIX-WHEN-EMPTY))
 (2 2 (:TYPE-PRESCRIPTION OMAP::EMPTY)))
(ACL2PL::SYMBOL-VALUEP-OF-HEAD-KEY-WHEN-BINDINGP
 (30 5
     (:REWRITE ACL2PL::SYMBOL-VALUEP-WHEN-MAYBE-SYMBOL-VALUEP))
 (25 1 (:REWRITE FAST-<<-IS-<<))
 (21 3
     (:REWRITE ACL2PL::MAYBE-SYMBOL-VALUEP-WHEN-SYMBOL-VALUEP))
 (19 5 (:REWRITE <<-TRICHOTOMY))
 (17 3 (:REWRITE <<-ASYMMETRIC))
 (14 14 (:REWRITE DEFAULT-CAR))
 (14 5
     (:REWRITE ACL2PL::SYMBOL-VALUEP-OF-CAR-WHEN-SYMBOL-VALUE-LISTP))
 (12 12 (:TYPE-PRESCRIPTION <<))
 (10 8
     (:TYPE-PRESCRIPTION OMAP::HEAD-KEY-WHEN-EMPTY))
 (8 8
    (:TYPE-PRESCRIPTION ACL2PL::MAYBE-SYMBOL-VALUEP))
 (8 2
    (:REWRITE ACL2PL::VALUEP-WHEN-MAYBE-VALUEP))
 (7 7 (:REWRITE DEFAULT-CDR))
 (7 7
    (:REWRITE CAR-OF-TRUE-LIST-LIST-FIX-X-NORMALIZE-CONST-UNDER-LIST-EQUIV))
 (6 6
    (:TYPE-PRESCRIPTION ACL2PL::SYMBOL-VALUE-LISTP))
 (5 5
    (:REWRITE ACL2PL::SYMBOL-VALUEP-WHEN-IN-SYMBOL-VALUE-SETP-BINDS-FREE-X))
 (5 5 (:REWRITE <<-TRANSITIVE))
 (5 1
    (:REWRITE ACL2PL::MAYBE-VALUEP-WHEN-VALUEP))
 (3 3
    (:TYPE-PRESCRIPTION ACL2PL::MAYBE-VALUEP))
 (3 3
    (:REWRITE ACL2PL::SYMBOL-VALUE-LISTP-WHEN-NOT-CONSP))
 (2 2 (:TYPE-PRESCRIPTION ACL2PL::VALUEP))
 (2
  2
  (:REWRITE
     CDR-OF-TRUE-LIST-LIST-FIX-X-NORMALIZE-CONST-UNDER-TRUE-LIST-LIST-EQUIV))
 (1 1 (:REWRITE OMAP::MFIX-WHEN-EMPTY)))
(ACL2PL::VALUEP-OF-HEAD-VAL-WHEN-BINDINGP
 (26 4
     (:REWRITE ACL2PL::SYMBOL-VALUEP-WHEN-MAYBE-SYMBOL-VALUEP))
 (25 1 (:REWRITE FAST-<<-IS-<<))
 (20 5
     (:REWRITE ACL2PL::VALUEP-WHEN-MAYBE-VALUEP))
 (20 2
     (:REWRITE ACL2PL::MAYBE-SYMBOL-VALUEP-WHEN-SYMBOL-VALUEP))
 (19 5 (:REWRITE <<-TRICHOTOMY))
 (17 3 (:REWRITE <<-ASYMMETRIC))
 (15 15 (:REWRITE DEFAULT-CAR))
 (12 12 (:TYPE-PRESCRIPTION <<))
 (11 3
     (:REWRITE ACL2PL::MAYBE-VALUEP-WHEN-VALUEP))
 (10 8
     (:TYPE-PRESCRIPTION OMAP::HEAD-VALUE-WHEN-EMPTY))
 (10 4
     (:REWRITE ACL2PL::SYMBOL-VALUEP-OF-CAR-WHEN-SYMBOL-VALUE-LISTP))
 (8 8
    (:TYPE-PRESCRIPTION ACL2PL::MAYBE-VALUEP))
 (8 8 (:REWRITE DEFAULT-CDR))
 (7 7
    (:REWRITE CAR-OF-TRUE-LIST-LIST-FIX-X-NORMALIZE-CONST-UNDER-LIST-EQUIV))
 (6 6
    (:TYPE-PRESCRIPTION ACL2PL::MAYBE-SYMBOL-VALUEP))
 (5 5 (:REWRITE <<-TRANSITIVE))
 (4 4
    (:TYPE-PRESCRIPTION ACL2PL::SYMBOL-VALUEP))
 (4 4
    (:REWRITE ACL2PL::SYMBOL-VALUEP-WHEN-IN-SYMBOL-VALUE-SETP-BINDS-FREE-X))
 (2 2
    (:REWRITE ACL2PL::SYMBOL-VALUE-LISTP-WHEN-NOT-CONSP))
 (2
  2
  (:REWRITE
     CDR-OF-TRUE-LIST-LIST-FIX-X-NORMALIZE-CONST-UNDER-TRUE-LIST-LIST-EQUIV))
 (1 1 (:REWRITE OMAP::MFIX-WHEN-EMPTY)))
(ACL2PL::BINDINGP-OF-UPDATE
 (803 703 (:REWRITE DEFAULT-CDR))
 (736 644 (:REWRITE <<-TRANSITIVE))
 (555
     555
     (:REWRITE CAR-OF-TRUE-LIST-LIST-FIX-X-NORMALIZE-CONST-UNDER-LIST-EQUIV))
 (377 135
      (:REWRITE ACL2PL::SYMBOL-VALUEP-OF-CAR-WHEN-SYMBOL-VALUE-LISTP))
 (236
     236
     (:REWRITE ACL2PL::SYMBOL-VALUEP-WHEN-IN-SYMBOL-VALUE-SETP-BINDS-FREE-X))
 (192
  192
  (:REWRITE
     CDR-OF-TRUE-LIST-LIST-FIX-X-NORMALIZE-CONST-UNDER-TRUE-LIST-LIST-EQUIV))
 (99 99 (:REWRITE OMAP::MFIX-WHEN-EMPTY))
 (88 88 (:TYPE-PRESCRIPTION OMAP::MFIX))
 (68 68
     (:REWRITE ACL2PL::SYMBOL-VALUE-LISTP-WHEN-NOT-CONSP))
 (49 49 (:REWRITE OMAP::TAIL-WHEN-EMPTY))
 (36
  36
  (:REWRITE
    CONS-OF-TRUE-LIST-LIST-FIX-Y-NORMALIZE-CONST-UNDER-TRUE-LIST-LIST-EQUIV))
 (36
    36
    (:REWRITE CONS-OF-LIST-FIX-X-NORMALIZE-CONST-UNDER-TRUE-LIST-LIST-EQUIV))
 (30 30 (:REWRITE OMAP::MAPP-WHEN-NOT-EMPTY))
 (25 25
     (:TYPE-PRESCRIPTION OMAP::HEAD-KEY-WHEN-EMPTY))
 (10 10 (:REWRITE <<-IRREFLEXIVE)))
(ACL2PL::BINDINGP-OF-UPDATE*
 (228 60 (:REWRITE <<-TRICHOTOMY))
 (204 36 (:REWRITE <<-ASYMMETRIC))
 (168 24
      (:REWRITE ACL2PL::SYMBOL-VALUEP-WHEN-MAYBE-SYMBOL-VALUEP))
 (132 12
      (:REWRITE ACL2PL::MAYBE-SYMBOL-VALUEP-WHEN-SYMBOL-VALUEP))
 (108 108 (:REWRITE DEFAULT-CAR))
 (102 24
      (:REWRITE ACL2PL::VALUEP-WHEN-MAYBE-VALUEP))
 (72 72 (:REWRITE DEFAULT-CDR))
 (66 24
     (:REWRITE ACL2PL::SYMBOL-VALUEP-OF-CAR-WHEN-SYMBOL-VALUE-LISTP))
 (66 12
     (:REWRITE ACL2PL::MAYBE-VALUEP-WHEN-VALUEP))
 (60 60
     (:REWRITE CAR-OF-TRUE-LIST-LIST-FIX-X-NORMALIZE-CONST-UNDER-LIST-EQUIV))
 (60 60 (:REWRITE <<-TRANSITIVE))
 (36 36
     (:TYPE-PRESCRIPTION ACL2PL::MAYBE-VALUEP))
 (36 36
     (:TYPE-PRESCRIPTION ACL2PL::MAYBE-SYMBOL-VALUEP))
 (24 24
     (:TYPE-PRESCRIPTION ACL2PL::SYMBOL-VALUE-LISTP))
 (24 24
     (:REWRITE ACL2PL::SYMBOL-VALUEP-WHEN-IN-SYMBOL-VALUE-SETP-BINDS-FREE-X))
 (24
  24
  (:REWRITE
     CDR-OF-TRUE-LIST-LIST-FIX-X-NORMALIZE-CONST-UNDER-TRUE-LIST-LIST-EQUIV))
 (18 6
     (:REWRITE OMAP::UPDATE*-WHEN-RIGHT-EMPTY))
 (12 12
     (:REWRITE ACL2PL::SYMBOL-VALUE-LISTP-WHEN-NOT-CONSP))
 (9 3 (:REWRITE OMAP::UPDATE-WHEN-EMPTY))
 (9 3 (:REWRITE OMAP::MFIX-WHEN-EMPTY))
 (3 3
    (:REWRITE OMAP::HEAD-VALUE-WHEN-EMPTY))
 (3 3 (:REWRITE OMAP::HEAD-KEY-WHEN-EMPTY))
 (2 2
    (:TYPE-PRESCRIPTION OMAP::HEAD-VALUE-WHEN-EMPTY))
 (2 2
    (:TYPE-PRESCRIPTION OMAP::HEAD-KEY-WHEN-EMPTY))
 (2 2 (:REWRITE OMAP::TAIL-WHEN-EMPTY)))
(ACL2PL::SYMBOL-VALUEP-WHEN-IN-BINDINGP-BINDS-FREE-X
 (249 14 (:REWRITE OMAP::IN-WHEN-IN-TAIL))
 (216 3 (:DEFINITION ACL2PL::BINDINGP))
 (122 84
      (:TYPE-PRESCRIPTION OMAP::TAIL-WHEN-EMPTY))
 (104 88
      (:TYPE-PRESCRIPTION OMAP::HEAD-KEY-WHEN-EMPTY))
 (75 3 (:REWRITE FAST-<<-IS-<<))
 (57 15 (:REWRITE <<-TRICHOTOMY))
 (57 10
     (:REWRITE ACL2PL::SYMBOL-VALUEP-WHEN-MAYBE-SYMBOL-VALUEP))
 (51 9 (:REWRITE <<-ASYMMETRIC))
 (42 5
     (:REWRITE ACL2PL::MAYBE-SYMBOL-VALUEP-WHEN-SYMBOL-VALUEP))
 (36 36 (:TYPE-PRESCRIPTION <<))
 (27 27 (:REWRITE DEFAULT-CAR))
 (24 6
     (:REWRITE ACL2PL::VALUEP-WHEN-MAYBE-VALUEP))
 (18 18 (:REWRITE DEFAULT-CDR))
 (18 10 (:REWRITE OMAP::TAIL-WHEN-EMPTY))
 (15 15
     (:TYPE-PRESCRIPTION ACL2PL::MAYBE-SYMBOL-VALUEP))
 (15 15
     (:REWRITE CAR-OF-TRUE-LIST-LIST-FIX-X-NORMALIZE-CONST-UNDER-LIST-EQUIV))
 (15 15 (:REWRITE <<-TRANSITIVE))
 (15 6
     (:REWRITE ACL2PL::SYMBOL-VALUEP-OF-CAR-WHEN-SYMBOL-VALUE-LISTP))
 (15 3
     (:REWRITE ACL2PL::MAYBE-VALUEP-WHEN-VALUEP))
 (13 5 (:REWRITE OMAP::IN-WHEN-EMPTY))
 (10 10
     (:REWRITE ACL2PL::SYMBOL-VALUEP-WHEN-IN-SYMBOL-VALUE-SETP-BINDS-FREE-X))
 (9 9
    (:TYPE-PRESCRIPTION ACL2PL::MAYBE-VALUEP))
 (9 9 (:REWRITE OMAP::HEAD-KEY-WHEN-EMPTY))
 (8 3
    (:TYPE-PRESCRIPTION OMAP::HEAD-VALUE-WHEN-EMPTY))
 (6 6 (:TYPE-PRESCRIPTION ACL2PL::VALUEP))
 (6 6
    (:TYPE-PRESCRIPTION ACL2PL::SYMBOL-VALUE-LISTP))
 (6 6
    (:REWRITE OMAP::HEAD-VALUE-WHEN-EMPTY))
 (6
  6
  (:REWRITE
     CDR-OF-TRUE-LIST-LIST-FIX-X-NORMALIZE-CONST-UNDER-TRUE-LIST-LIST-EQUIV))
 (3 3
    (:REWRITE ACL2PL::SYMBOL-VALUE-LISTP-WHEN-NOT-CONSP)))
(ACL2PL::SYMBOL-VALUEP-OF-CAR-OF-IN-BINDINGP
 (370 5 (:DEFINITION ACL2PL::BINDINGP))
 (258 15 (:REWRITE OMAP::IN-WHEN-IN-TAIL))
 (167 127
      (:TYPE-PRESCRIPTION OMAP::TAIL-WHEN-EMPTY))
 (130 114
      (:TYPE-PRESCRIPTION OMAP::HEAD-KEY-WHEN-EMPTY))
 (125 5 (:REWRITE FAST-<<-IS-<<))
 (95 25 (:REWRITE <<-TRICHOTOMY))
 (85 15 (:REWRITE <<-ASYMMETRIC))
 (76 16
     (:REWRITE ACL2PL::SYMBOL-VALUEP-OF-CAR-WHEN-SYMBOL-VALUE-LISTP))
 (63 50 (:REWRITE DEFAULT-CAR))
 (60 60 (:TYPE-PRESCRIPTION <<))
 (40 10
     (:REWRITE ACL2PL::VALUEP-WHEN-MAYBE-VALUEP))
 (30 30 (:REWRITE DEFAULT-CDR))
 (28 12 (:REWRITE OMAP::IN-WHEN-EMPTY))
 (25 25
     (:REWRITE CAR-OF-TRUE-LIST-LIST-FIX-X-NORMALIZE-CONST-UNDER-LIST-EQUIV))
 (25 25 (:REWRITE <<-TRANSITIVE))
 (25 5
     (:REWRITE ACL2PL::MAYBE-VALUEP-WHEN-VALUEP))
 (20 12 (:REWRITE OMAP::TAIL-WHEN-EMPTY))
 (20 8
     (:REWRITE ACL2PL::SYMBOL-VALUE-LISTP-WHEN-NOT-CONSP))
 (18 18
     (:REWRITE ACL2PL::SYMBOL-VALUEP-WHEN-IN-BINDINGP-BINDS-FREE-X))
 (17 17
     (:REWRITE ACL2PL::SYMBOL-VALUEP-WHEN-IN-SYMBOL-VALUE-SETP-BINDS-FREE-X))
 (16 16
     (:TYPE-PRESCRIPTION ACL2PL::SYMBOL-VALUE-LISTP))
 (15 15
     (:TYPE-PRESCRIPTION ACL2PL::MAYBE-VALUEP))
 (15 15 (:REWRITE OMAP::HEAD-KEY-WHEN-EMPTY))
 (11 11
     (:REWRITE OMAP::HEAD-VALUE-WHEN-EMPTY))
 (10 10 (:TYPE-PRESCRIPTION ACL2PL::VALUEP))
 (10
  10
  (:REWRITE
     CDR-OF-TRUE-LIST-LIST-FIX-X-NORMALIZE-CONST-UNDER-TRUE-LIST-LIST-EQUIV))
 (9 4
    (:TYPE-PRESCRIPTION OMAP::HEAD-VALUE-WHEN-EMPTY)))
(ACL2PL::VALUEP-OF-CDR-OF-IN-BINDINGP
 (370 5 (:DEFINITION ACL2PL::BINDINGP))
 (258 15 (:REWRITE OMAP::IN-WHEN-IN-TAIL))
 (172 132
      (:TYPE-PRESCRIPTION OMAP::TAIL-WHEN-EMPTY))
 (129 113
      (:TYPE-PRESCRIPTION OMAP::HEAD-KEY-WHEN-EMPTY))
 (125 5 (:REWRITE FAST-<<-IS-<<))
 (95 25 (:REWRITE <<-TRICHOTOMY))
 (85 15 (:REWRITE <<-ASYMMETRIC))
 (70 10
     (:REWRITE ACL2PL::SYMBOL-VALUEP-WHEN-MAYBE-SYMBOL-VALUEP))
 (60 60 (:TYPE-PRESCRIPTION <<))
 (55 5
     (:REWRITE ACL2PL::MAYBE-SYMBOL-VALUEP-WHEN-SYMBOL-VALUEP))
 (48 35 (:REWRITE DEFAULT-CDR))
 (45 45 (:REWRITE DEFAULT-CAR))
 (28 12 (:REWRITE OMAP::IN-WHEN-EMPTY))
 (25 25
     (:REWRITE CAR-OF-TRUE-LIST-LIST-FIX-X-NORMALIZE-CONST-UNDER-LIST-EQUIV))
 (25 25 (:REWRITE <<-TRANSITIVE))
 (25 10
     (:REWRITE ACL2PL::SYMBOL-VALUEP-OF-CAR-WHEN-SYMBOL-VALUE-LISTP))
 (20 12 (:REWRITE OMAP::TAIL-WHEN-EMPTY))
 (15 15
     (:TYPE-PRESCRIPTION ACL2PL::MAYBE-SYMBOL-VALUEP))
 (15 15 (:REWRITE OMAP::HEAD-KEY-WHEN-EMPTY))
 (11 11
     (:REWRITE OMAP::HEAD-VALUE-WHEN-EMPTY))
 (10 10
     (:TYPE-PRESCRIPTION ACL2PL::SYMBOL-VALUEP))
 (10 10
     (:REWRITE ACL2PL::SYMBOL-VALUEP-WHEN-IN-SYMBOL-VALUE-SETP-BINDS-FREE-X))
 (10 10
     (:REWRITE ACL2PL::SYMBOL-VALUEP-WHEN-IN-BINDINGP-BINDS-FREE-X))
 (10
  10
  (:REWRITE
     CDR-OF-TRUE-LIST-LIST-FIX-X-NORMALIZE-CONST-UNDER-TRUE-LIST-LIST-EQUIV))
 (10 5
     (:TYPE-PRESCRIPTION OMAP::HEAD-VALUE-WHEN-EMPTY))
 (5 5
    (:REWRITE ACL2PL::SYMBOL-VALUE-LISTP-WHEN-NOT-CONSP)))
(ACL2PL::BINDING-FIX (1 1
                        (:TYPE-PRESCRIPTION ACL2PL::BINDING-FIX)))
(ACL2PL::BINDINGP-OF-BINDING-FIX)
(ACL2PL::BINDING-FIX-WHEN-BINDINGP)
(ACL2PL::EMPTY-OF-BINDING-FIX
     (28 7 (:REWRITE OMAP::MFIX-WHEN-EMPTY))
     (14 14
         (:TYPE-PRESCRIPTION ACL2PL::BINDING-FIX))
     (10 2 (:REWRITE OMAP::MAPP-WHEN-NOT-EMPTY))
     (3 1
        (:REWRITE ACL2PL::BINDING-FIX-WHEN-BINDINGP)))
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT
     (33 33
         (:TYPE-PRESCRIPTION ACL2PL::BINDING-FIX)))
(ACL2PL::BINDING-EQUIV$INLINE (4 4
                                 (:TYPE-PRESCRIPTION ACL2PL::BINDING-FIX)))
(ACL2PL::BINDING-EQUIV-IS-AN-EQUIVALENCE)
(ACL2PL::BINDING-EQUIV-IMPLIES-EQUAL-BINDING-FIX-1)
(ACL2PL::BINDING-FIX-UNDER-BINDING-EQUIV)
(ACL2PL::EQUAL-OF-BINDING-FIX-1-FORWARD-TO-BINDING-EQUIV)
(ACL2PL::EQUAL-OF-BINDING-FIX-2-FORWARD-TO-BINDING-EQUIV)
(ACL2PL::BINDING-EQUIV-OF-BINDING-FIX-1-FORWARD)
(ACL2PL::BINDING-EQUIV-OF-BINDING-FIX-2-FORWARD)
(ACL2PL::BINDINGP-OF-FROM-LISTS
  (20 10 (:REWRITE DEFAULT-+-2))
  (12 4 (:REWRITE OMAP::UPDATE-WHEN-EMPTY))
  (10 10 (:REWRITE DEFAULT-CDR))
  (10 10 (:REWRITE DEFAULT-+-1))
  (8 8 (:TYPE-PRESCRIPTION OMAP::EMPTY))
  (8 8 (:REWRITE DEFAULT-CAR))
  (7 7
     (:REWRITE ACL2PL::SYMBOL-VALUE-LISTP-WHEN-NOT-CONSP))
  (5 1
     (:REWRITE ACL2PL::VALUEP-WHEN-MAYBE-VALUEP))
  (5 1
     (:REWRITE ACL2PL::SYMBOL-VALUEP-WHEN-MAYBE-SYMBOL-VALUEP))
  (2 2
     (:TYPE-PRESCRIPTION ACL2PL::MAYBE-VALUEP))
  (2 2
     (:TYPE-PRESCRIPTION ACL2PL::MAYBE-SYMBOL-VALUEP))
  (2 1
     (:REWRITE ACL2PL::MAYBE-VALUEP-WHEN-VALUEP))
  (2 1
     (:REWRITE ACL2PL::MAYBE-SYMBOL-VALUEP-WHEN-SYMBOL-VALUEP))
  (1 1
     (:REWRITE ACL2PL::SYMBOL-VALUEP-WHEN-IN-SYMBOL-VALUE-SETP-BINDS-FREE-X))
  (1 1
     (:REWRITE ACL2PL::SYMBOL-VALUEP-WHEN-IN-BINDINGP-BINDS-FREE-X)))
(ACL2PL::FRAMEP)
(ACL2PL::CONSP-WHEN-FRAMEP)
(ACL2PL::TAG-WHEN-FRAMEP)
(ACL2PL::FRAMEP-WHEN-WRONG-TAG)
(ACL2PL::FRAME-FIX$INLINE (6 6
                             (:TYPE-PRESCRIPTION ACL2PL::BINDING-FIX)))
(ACL2PL::FRAMEP-OF-FRAME-FIX
     (12 4
         (:REWRITE ACL2PL::TTERM-FIX-WHEN-TTERMP))
     (12 4
         (:REWRITE ACL2PL::BINDING-FIX-WHEN-BINDINGP))
     (8 8 (:TYPE-PRESCRIPTION ACL2PL::TTERMP))
     (8 8
        (:TYPE-PRESCRIPTION ACL2PL::BINDINGP)))
(ACL2PL::FRAME-FIX-WHEN-FRAMEP)
(ACL2PL::FRAME-FIX$INLINE (6 6
                             (:TYPE-PRESCRIPTION ACL2PL::BINDING-FIX)))
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT)
(ACL2PL::FRAME-EQUIV$INLINE)
(ACL2PL::FRAME-EQUIV-IS-AN-EQUIVALENCE)
(ACL2PL::FRAME-EQUIV-IMPLIES-EQUAL-FRAME-FIX-1)
(ACL2PL::FRAME-FIX-UNDER-FRAME-EQUIV)
(ACL2PL::EQUAL-OF-FRAME-FIX-1-FORWARD-TO-FRAME-EQUIV)
(ACL2PL::EQUAL-OF-FRAME-FIX-2-FORWARD-TO-FRAME-EQUIV)
(ACL2PL::FRAME-EQUIV-OF-FRAME-FIX-1-FORWARD)
(ACL2PL::FRAME-EQUIV-OF-FRAME-FIX-2-FORWARD)
(ACL2PL::TAG-OF-FRAME-FIX)
(ACL2PL::FRAME->TERM$INLINE)
(ACL2PL::TTERMP-OF-FRAME->TERM)
(ACL2PL::FRAME->TERM$INLINE-OF-FRAME-FIX-X
     (9 3
        (:REWRITE ACL2PL::FRAME-FIX-WHEN-FRAMEP))
     (6 6 (:TYPE-PRESCRIPTION ACL2PL::FRAMEP))
     (3 1
        (:REWRITE ACL2PL::BINDING-FIX-WHEN-BINDINGP))
     (2 2
        (:TYPE-PRESCRIPTION ACL2PL::BINDINGP)))
(ACL2PL::FRAME->TERM$INLINE-OF-FRAME-FIX-X-NORMALIZE-CONST)
(ACL2PL::FRAME->TERM$INLINE-FRAME-EQUIV-CONGRUENCE-ON-X)
(ACL2PL::FRAME->BINDING$INLINE (20 20
                                   (:TYPE-PRESCRIPTION ACL2PL::BINDING-FIX)))
(ACL2PL::BINDINGP-OF-FRAME->BINDING)
(ACL2PL::FRAME->BINDING$INLINE-OF-FRAME-FIX-X
     (69 46
         (:TYPE-PRESCRIPTION ACL2PL::BINDING-FIX))
     (23 23
         (:TYPE-PRESCRIPTION ACL2PL::FRAME-FIX$INLINE))
     (9 3
        (:REWRITE ACL2PL::FRAME-FIX-WHEN-FRAMEP))
     (6 6 (:TYPE-PRESCRIPTION ACL2PL::FRAMEP))
     (3 1
        (:REWRITE ACL2PL::TTERM-FIX-WHEN-TTERMP))
     (2 2 (:TYPE-PRESCRIPTION ACL2PL::TTERMP)))
(ACL2PL::FRAME->BINDING$INLINE-OF-FRAME-FIX-X-NORMALIZE-CONST)
(ACL2PL::FRAME->BINDING$INLINE-FRAME-EQUIV-CONGRUENCE-ON-X)
(ACL2PL::FRAME)
(ACL2PL::FRAMEP-OF-FRAME)
(ACL2PL::FRAME->TERM-OF-FRAME)
(ACL2PL::FRAME->BINDING-OF-FRAME
     (81 63
         (:TYPE-PRESCRIPTION ACL2PL::BINDING-FIX))
     (18 18 (:TYPE-PRESCRIPTION ACL2PL::FRAME)))
(ACL2PL::FRAME-OF-FIELDS (3 1
                            (:REWRITE ACL2PL::FRAME-FIX-WHEN-FRAMEP))
                         (2 2 (:TYPE-PRESCRIPTION ACL2PL::FRAMEP)))
(ACL2PL::FRAME-FIX-WHEN-FRAME (3 1
                                 (:REWRITE ACL2PL::FRAME-FIX-WHEN-FRAMEP))
                              (2 2 (:TYPE-PRESCRIPTION ACL2PL::FRAMEP)))
(ACL2PL::EQUAL-OF-FRAME
 (9 9
    (:REWRITE ACL2PL::FRAME->TERM$INLINE-OF-FRAME-FIX-X-NORMALIZE-CONST))
 (6 6
    (:REWRITE ACL2PL::FRAME->BINDING$INLINE-OF-FRAME-FIX-X-NORMALIZE-CONST)))
(ACL2PL::FRAME-OF-TTERM-FIX-TERM
     (4 2
        (:REWRITE ACL2PL::BINDING-FIX-WHEN-BINDINGP))
     (2 2
        (:TYPE-PRESCRIPTION ACL2PL::BINDINGP)))
(ACL2PL::FRAME-OF-TTERM-FIX-TERM-NORMALIZE-CONST)
(ACL2PL::FRAME-TTERM-EQUIV-CONGRUENCE-ON-TERM)
(ACL2PL::FRAME-OF-BINDING-FIX-BINDING
     (4 2
        (:REWRITE ACL2PL::TTERM-FIX-WHEN-TTERMP))
     (2 2 (:TYPE-PRESCRIPTION ACL2PL::TTERMP)))
(ACL2PL::FRAME-OF-BINDING-FIX-BINDING-NORMALIZE-CONST)
(ACL2PL::FRAME-BINDING-EQUIV-CONGRUENCE-ON-BINDING)
(ACL2PL::FRAME-FIX-REDEF)
(ACL2PL::TAG-OF-FRAME)
(ACL2PL::STACKP)
(STD::DEFLIST-LOCAL-BOOLEANP-ELEMENT-THM)
(STD::DEFLIST-LOCAL-ELEMENTP-OF-NIL-THM)
(ACL2PL::STACKP-OF-CONS)
(ACL2PL::STACKP-OF-CDR-WHEN-STACKP)
(ACL2PL::STACKP-WHEN-NOT-CONSP)
(ACL2PL::FRAMEP-OF-CAR-WHEN-STACKP)
(ACL2PL::TRUE-LISTP-WHEN-STACKP)
(ACL2PL::STACKP-OF-LIST-FIX)
(ACL2PL::STACKP-OF-REV)
(ACL2PL::STACKP-OF-APPEND)
(ACL2PL::STACK-FIX$INLINE)
(ACL2PL::STACKP-OF-STACK-FIX
     (15 1
         (:REWRITE ACL2PL::FRAME-FIX-WHEN-FRAMEP))
     (12 2
         (:REWRITE ACL2PL::FRAMEP-OF-CAR-WHEN-STACKP))
     (9 5
        (:REWRITE ACL2PL::STACKP-WHEN-NOT-CONSP))
     (9 1 (:DEFINITION ACL2PL::STACKP))
     (4 4 (:TYPE-PRESCRIPTION ACL2PL::FRAMEP))
     (2 1
        (:REWRITE ACL2PL::STACKP-OF-CDR-WHEN-STACKP)))
(ACL2PL::STACK-FIX-WHEN-STACKP
     (17 4
         (:REWRITE ACL2PL::STACKP-OF-CDR-WHEN-STACKP))
     (9 3
        (:REWRITE ACL2PL::FRAMEP-OF-CAR-WHEN-STACKP)))
(ACL2PL::STACK-FIX$INLINE (4 4
                             (:REWRITE ACL2PL::STACKP-WHEN-NOT-CONSP))
                          (4 1
                             (:REWRITE ACL2PL::STACKP-OF-CDR-WHEN-STACKP))
                          (4 1
                             (:REWRITE ACL2PL::FRAMEP-OF-CAR-WHEN-STACKP)))
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT (1 1
                                   (:REWRITE ACL2PL::STACKP-WHEN-NOT-CONSP)))
(ACL2PL::STACK-EQUIV$INLINE)
(ACL2PL::STACK-EQUIV-IS-AN-EQUIVALENCE)
(ACL2PL::STACK-EQUIV-IMPLIES-EQUAL-STACK-FIX-1)
(ACL2PL::STACK-FIX-UNDER-STACK-EQUIV)
(ACL2PL::EQUAL-OF-STACK-FIX-1-FORWARD-TO-STACK-EQUIV)
(ACL2PL::EQUAL-OF-STACK-FIX-2-FORWARD-TO-STACK-EQUIV)
(ACL2PL::STACK-EQUIV-OF-STACK-FIX-1-FORWARD)
(ACL2PL::STACK-EQUIV-OF-STACK-FIX-2-FORWARD)
(ACL2PL::CAR-OF-STACK-FIX-X-UNDER-FRAME-EQUIV
     (21 3
         (:REWRITE ACL2PL::FRAME-FIX-WHEN-FRAMEP))
     (12 12 (:TYPE-PRESCRIPTION ACL2PL::STACKP))
     (12 3
         (:REWRITE ACL2PL::FRAMEP-OF-CAR-WHEN-STACKP))
     (12 2
         (:REWRITE ACL2PL::STACK-FIX-WHEN-STACKP))
     (6 6 (:TYPE-PRESCRIPTION ACL2PL::FRAMEP))
     (6 6
        (:REWRITE ACL2PL::STACKP-WHEN-NOT-CONSP))
     (4 1
        (:REWRITE ACL2PL::STACKP-OF-CDR-WHEN-STACKP))
     (3 3
        (:TYPE-PRESCRIPTION ACL2PL::STACK-FIX$INLINE)))
(ACL2PL::CAR-OF-STACK-FIX-X-NORMALIZE-CONST-UNDER-FRAME-EQUIV)
(ACL2PL::CAR-STACK-EQUIV-CONGRUENCE-ON-X-UNDER-FRAME-EQUIV)
(ACL2PL::CDR-OF-STACK-FIX-X-UNDER-STACK-EQUIV
     (29 3
         (:REWRITE ACL2PL::STACKP-OF-CDR-WHEN-STACKP))
     (14 2
         (:REWRITE ACL2PL::FRAME-FIX-WHEN-FRAMEP))
     (8 2
        (:REWRITE ACL2PL::FRAMEP-OF-CAR-WHEN-STACKP))
     (4 4 (:TYPE-PRESCRIPTION ACL2PL::FRAMEP)))
(ACL2PL::CDR-OF-STACK-FIX-X-NORMALIZE-CONST-UNDER-STACK-EQUIV)
(ACL2PL::CDR-STACK-EQUIV-CONGRUENCE-ON-X-UNDER-STACK-EQUIV)
(ACL2PL::CONS-OF-FRAME-FIX-X-UNDER-STACK-EQUIV
 (20 4
     (:REWRITE ACL2PL::STACK-FIX-WHEN-STACKP))
 (9 2 (:REWRITE ACL2PL::STACKP-OF-CONS))
 (6 6 (:TYPE-PRESCRIPTION ACL2PL::STACKP))
 (5 5
    (:REWRITE ACL2PL::STACKP-WHEN-NOT-CONSP))
 (2 2
    (:REWRITE ACL2PL::CDR-OF-STACK-FIX-X-NORMALIZE-CONST-UNDER-STACK-EQUIV)))
(ACL2PL::CONS-OF-FRAME-FIX-X-NORMALIZE-CONST-UNDER-STACK-EQUIV)
(ACL2PL::CONS-FRAME-EQUIV-CONGRUENCE-ON-X-UNDER-STACK-EQUIV)
(ACL2PL::CONS-OF-STACK-FIX-Y-UNDER-STACK-EQUIV
 (12 2 (:REWRITE ACL2PL::STACKP-OF-CONS))
 (8 8 (:TYPE-PRESCRIPTION ACL2PL::FRAMEP))
 (5 4
    (:REWRITE ACL2PL::STACKP-WHEN-NOT-CONSP))
 (4 2
    (:REWRITE ACL2PL::FRAME-FIX-WHEN-FRAMEP))
 (2 2
    (:REWRITE ACL2PL::CONS-OF-FRAME-FIX-X-NORMALIZE-CONST-UNDER-STACK-EQUIV))
 (2 2
    (:REWRITE ACL2PL::CDR-OF-STACK-FIX-X-NORMALIZE-CONST-UNDER-STACK-EQUIV)))
(ACL2PL::CONS-OF-STACK-FIX-Y-NORMALIZE-CONST-UNDER-STACK-EQUIV)
(ACL2PL::CONS-STACK-EQUIV-CONGRUENCE-ON-Y-UNDER-STACK-EQUIV)
(ACL2PL::CONSP-OF-STACK-FIX
 (12 2
     (:REWRITE ACL2PL::STACK-FIX-WHEN-STACKP))
 (8 8 (:TYPE-PRESCRIPTION ACL2PL::STACKP))
 (7 1
    (:REWRITE ACL2PL::FRAME-FIX-WHEN-FRAMEP))
 (4 4
    (:REWRITE ACL2PL::STACKP-WHEN-NOT-CONSP))
 (4 1
    (:REWRITE ACL2PL::STACKP-OF-CDR-WHEN-STACKP))
 (4 1
    (:REWRITE ACL2PL::FRAMEP-OF-CAR-WHEN-STACKP))
 (2 2 (:TYPE-PRESCRIPTION ACL2PL::FRAMEP))
 (1 1
    (:REWRITE ACL2PL::CDR-OF-STACK-FIX-X-NORMALIZE-CONST-UNDER-STACK-EQUIV)))
(ACL2PL::STACK-FIX-UNDER-IFF
 (12 2
     (:REWRITE ACL2PL::STACK-FIX-WHEN-STACKP))
 (8 8 (:TYPE-PRESCRIPTION ACL2PL::STACKP))
 (7 1
    (:REWRITE ACL2PL::FRAME-FIX-WHEN-FRAMEP))
 (4 4
    (:REWRITE ACL2PL::STACKP-WHEN-NOT-CONSP))
 (4 1
    (:REWRITE ACL2PL::STACKP-OF-CDR-WHEN-STACKP))
 (4 1
    (:REWRITE ACL2PL::FRAMEP-OF-CAR-WHEN-STACKP))
 (2 2 (:TYPE-PRESCRIPTION ACL2PL::FRAMEP))
 (1 1
    (:REWRITE ACL2PL::CDR-OF-STACK-FIX-X-NORMALIZE-CONST-UNDER-STACK-EQUIV)))
(ACL2PL::STACK-FIX-OF-CONS
 (13 3
     (:REWRITE ACL2PL::STACK-FIX-WHEN-STACKP))
 (5 1 (:REWRITE ACL2PL::STACKP-OF-CONS))
 (4 4 (:TYPE-PRESCRIPTION ACL2PL::STACKP))
 (4 4 (:TYPE-PRESCRIPTION ACL2PL::FRAMEP))
 (4 2
    (:REWRITE ACL2PL::FRAME-FIX-WHEN-FRAMEP))
 (3 3
    (:REWRITE ACL2PL::STACKP-WHEN-NOT-CONSP))
 (1 1
    (:REWRITE ACL2PL::CONS-OF-STACK-FIX-Y-NORMALIZE-CONST-UNDER-STACK-EQUIV))
 (1 1
    (:REWRITE ACL2PL::CONS-OF-FRAME-FIX-X-NORMALIZE-CONST-UNDER-STACK-EQUIV))
 (1 1
    (:REWRITE ACL2PL::CDR-OF-STACK-FIX-X-NORMALIZE-CONST-UNDER-STACK-EQUIV)))
(ACL2PL::LEN-OF-STACK-FIX
  (23 4
      (:REWRITE ACL2PL::STACK-FIX-WHEN-STACKP))
  (13 13 (:TYPE-PRESCRIPTION ACL2PL::STACKP))
  (8 2
     (:REWRITE ACL2PL::STACKP-OF-CDR-WHEN-STACKP))
  (7 7
     (:REWRITE ACL2PL::STACKP-WHEN-NOT-CONSP))
  (7 1
     (:REWRITE ACL2PL::FRAME-FIX-WHEN-FRAMEP))
  (4 1
     (:REWRITE ACL2PL::FRAMEP-OF-CAR-WHEN-STACKP))
  (2 2 (:TYPE-PRESCRIPTION ACL2PL::FRAMEP))
  (2 2
     (:REWRITE ACL2PL::CDR-OF-STACK-FIX-X-NORMALIZE-CONST-UNDER-STACK-EQUIV))
  (1 1 (:REWRITE FTY::EQUAL-OF-LEN)))
(ACL2PL::STACK-FIX-OF-APPEND
 (76 10
     (:REWRITE ACL2PL::STACK-FIX-WHEN-STACKP))
 (38 2 (:REWRITE ACL2PL::STACKP-OF-APPEND))
 (29 29 (:TYPE-PRESCRIPTION ACL2PL::STACKP))
 (22 16
     (:REWRITE ACL2PL::STACKP-WHEN-NOT-CONSP))
 (16 2 (:REWRITE ACL2PL::STACKP-OF-LIST-FIX))
 (12 12 (:TYPE-PRESCRIPTION TRUE-LIST-FIX))
 (10 4
     (:REWRITE ACL2PL::STACKP-OF-CDR-WHEN-STACKP))
 (8 2
    (:REWRITE ACL2PL::FRAME-FIX-WHEN-FRAMEP))
 (4 1
    (:REWRITE ACL2PL::FRAMEP-OF-CAR-WHEN-STACKP))
 (2 2 (:TYPE-PRESCRIPTION ACL2PL::FRAMEP))
 (2 2
    (:REWRITE ACL2PL::CDR-OF-STACK-FIX-X-NORMALIZE-CONST-UNDER-STACK-EQUIV))
 (1 1
    (:REWRITE ACL2PL::CONS-OF-STACK-FIX-Y-NORMALIZE-CONST-UNDER-STACK-EQUIV))
 (1 1
    (:REWRITE ACL2PL::CONS-OF-FRAME-FIX-X-NORMALIZE-CONST-UNDER-STACK-EQUIV))
 (1 1
    (:REWRITE ACL2PL::CAR-OF-STACK-FIX-X-NORMALIZE-CONST-UNDER-FRAME-EQUIV)))
(ACL2PL::EVAL-STATE-P)
(ACL2PL::CONSP-WHEN-EVAL-STATE-P)
(ACL2PL::EVAL-STATE-KIND$INLINE)
(ACL2PL::EVAL-STATE-KIND-POSSIBILITIES)
(ACL2PL::EVAL-STATE-FIX$INLINE)
(ACL2PL::EVAL-STATE-P-OF-EVAL-STATE-FIX
     (12 4
         (:REWRITE ACL2PL::VALUE-LIST-FIX-WHEN-VALUE-LISTP))
     (12 4
         (:REWRITE ACL2PL::VALUE-FIX-WHEN-VALUEP))
     (12 4
         (:REWRITE ACL2PL::SYMBOL-VALUE-FIX-WHEN-SYMBOL-VALUEP))
     (12 4
         (:REWRITE ACL2PL::STACK-FIX-WHEN-STACKP))
     (8 8 (:TYPE-PRESCRIPTION ACL2PL::VALUEP))
     (8 8
        (:TYPE-PRESCRIPTION ACL2PL::VALUE-LISTP))
     (8 8
        (:TYPE-PRESCRIPTION ACL2PL::SYMBOL-VALUEP))
     (8 8 (:TYPE-PRESCRIPTION ACL2PL::STACKP)))
(ACL2PL::EVAL-STATE-FIX-WHEN-EVAL-STATE-P)
(ACL2PL::EVAL-STATE-FIX$INLINE)
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT)
(ACL2PL::EVAL-STATE-EQUIV$INLINE)
(ACL2PL::EVAL-STATE-EQUIV-IS-AN-EQUIVALENCE)
(ACL2PL::EVAL-STATE-EQUIV-IMPLIES-EQUAL-EVAL-STATE-FIX-1)
(ACL2PL::EVAL-STATE-FIX-UNDER-EVAL-STATE-EQUIV)
(ACL2PL::EQUAL-OF-EVAL-STATE-FIX-1-FORWARD-TO-EVAL-STATE-EQUIV)
(ACL2PL::EQUAL-OF-EVAL-STATE-FIX-2-FORWARD-TO-EVAL-STATE-EQUIV)
(ACL2PL::EVAL-STATE-EQUIV-OF-EVAL-STATE-FIX-1-FORWARD)
(ACL2PL::EVAL-STATE-EQUIV-OF-EVAL-STATE-FIX-2-FORWARD)
(ACL2PL::EVAL-STATE-KIND$INLINE-OF-EVAL-STATE-FIX-X
     (13 9
         (:REWRITE ACL2PL::VALUE-LIST-FIX-WHEN-VALUE-LISTP))
     (13 9
         (:REWRITE ACL2PL::SYMBOL-VALUE-FIX-WHEN-SYMBOL-VALUEP))
     (7 5
        (:REWRITE ACL2PL::VALUE-FIX-WHEN-VALUEP))
     (7 5
        (:REWRITE ACL2PL::STACK-FIX-WHEN-STACKP))
     (4 4
        (:TYPE-PRESCRIPTION ACL2PL::VALUE-LISTP))
     (4 4
        (:TYPE-PRESCRIPTION ACL2PL::SYMBOL-VALUEP))
     (2 2 (:TYPE-PRESCRIPTION ACL2PL::VALUEP))
     (2 2 (:TYPE-PRESCRIPTION ACL2PL::STACKP))
     (1 1
        (:REWRITE ACL2PL::EVAL-STATE-FIX-WHEN-EVAL-STATE-P)))
(ACL2PL::EVAL-STATE-KIND$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST)
(ACL2PL::EVAL-STATE-KIND$INLINE-EVAL-STATE-EQUIV-CONGRUENCE-ON-X)
(ACL2PL::CONSP-OF-EVAL-STATE-FIX)
(ACL2PL::TAG-WHEN-EVAL-STATE-P-FORWARD
 (4
   4
   (:REWRITE
        ACL2PL::EVAL-STATE-KIND$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST)))
(ACL2PL::TAG-OF-EVAL-STATE-FIX)
(ACL2PL::EVAL-STATE-INIT->FUNCTION$INLINE
 (2
   2
   (:REWRITE
        ACL2PL::EVAL-STATE-KIND$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST)))
(ACL2PL::SYMBOL-VALUEP-OF-EVAL-STATE-INIT->FUNCTION
 (3 1
    (:REWRITE ACL2PL::SYMBOL-VALUE-FIX-WHEN-SYMBOL-VALUEP))
 (1
   1
   (:REWRITE
        ACL2PL::EVAL-STATE-KIND$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST)))
(ACL2PL::EVAL-STATE-INIT->FUNCTION$INLINE-OF-EVAL-STATE-FIX-X
 (13 5
     (:REWRITE ACL2PL::EVAL-STATE-FIX-WHEN-EVAL-STATE-P))
 (8 8
    (:TYPE-PRESCRIPTION ACL2PL::EVAL-STATE-P))
 (8 8
    (:REWRITE
         ACL2PL::EVAL-STATE-KIND$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST))
 (6 2
    (:REWRITE ACL2PL::VALUE-LIST-FIX-WHEN-VALUE-LISTP))
 (4 4
    (:TYPE-PRESCRIPTION ACL2PL::VALUE-LISTP)))
(ACL2PL::EVAL-STATE-INIT->FUNCTION$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST)
(ACL2PL::EVAL-STATE-INIT->FUNCTION$INLINE-EVAL-STATE-EQUIV-CONGRUENCE-ON-X)
(ACL2PL::EVAL-STATE-INIT->FUNCTION-WHEN-WRONG-KIND
 (6 2
    (:REWRITE ACL2PL::SYMBOL-VALUE-FIX-WHEN-SYMBOL-VALUEP))
 (4 4
    (:TYPE-PRESCRIPTION ACL2PL::SYMBOL-VALUEP))
 (2 2
    (:REWRITE
         ACL2PL::EVAL-STATE-KIND$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST))
 (1
  1
  (:REWRITE
   ACL2PL::EVAL-STATE-INIT->FUNCTION$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST)))
(ACL2PL::EVAL-STATE-INIT->ARGUMENTS$INLINE
 (2
   2
   (:REWRITE
        ACL2PL::EVAL-STATE-KIND$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST)))
(ACL2PL::VALUE-LISTP-OF-EVAL-STATE-INIT->ARGUMENTS
 (3 1
    (:REWRITE ACL2PL::VALUE-LIST-FIX-WHEN-VALUE-LISTP))
 (1
   1
   (:REWRITE
        ACL2PL::EVAL-STATE-KIND$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST)))
(ACL2PL::EVAL-STATE-INIT->ARGUMENTS$INLINE-OF-EVAL-STATE-FIX-X
 (13 5
     (:REWRITE ACL2PL::EVAL-STATE-FIX-WHEN-EVAL-STATE-P))
 (8 8
    (:TYPE-PRESCRIPTION ACL2PL::EVAL-STATE-P))
 (8 8
    (:REWRITE
         ACL2PL::EVAL-STATE-KIND$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST))
 (6 2
    (:REWRITE ACL2PL::SYMBOL-VALUE-FIX-WHEN-SYMBOL-VALUEP))
 (4 4
    (:TYPE-PRESCRIPTION ACL2PL::SYMBOL-VALUEP)))
(ACL2PL::EVAL-STATE-INIT->ARGUMENTS$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST)
(ACL2PL::EVAL-STATE-INIT->ARGUMENTS$INLINE-EVAL-STATE-EQUIV-CONGRUENCE-ON-X)
(ACL2PL::EVAL-STATE-INIT->ARGUMENTS-WHEN-WRONG-KIND
 (6 2
    (:REWRITE ACL2PL::VALUE-LIST-FIX-WHEN-VALUE-LISTP))
 (4 4
    (:TYPE-PRESCRIPTION ACL2PL::VALUE-LISTP))
 (2 2
    (:REWRITE
         ACL2PL::EVAL-STATE-KIND$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST))
 (1
  1
  (:REWRITE
   ACL2PL::EVAL-STATE-INIT->ARGUMENTS$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST)))
(ACL2PL::EVAL-STATE-INIT)
(ACL2PL::RETURN-TYPE-OF-EVAL-STATE-INIT
 (3 1
    (:REWRITE ACL2PL::VALUE-LIST-FIX-WHEN-VALUE-LISTP))
 (3 1
    (:REWRITE ACL2PL::SYMBOL-VALUE-FIX-WHEN-SYMBOL-VALUEP))
 (2 2
    (:TYPE-PRESCRIPTION ACL2PL::VALUE-LISTP))
 (2 2
    (:TYPE-PRESCRIPTION ACL2PL::SYMBOL-VALUEP))
 (1
   1
   (:REWRITE
        ACL2PL::EVAL-STATE-KIND$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST)))
(ACL2PL::EVAL-STATE-INIT->FUNCTION-OF-EVAL-STATE-INIT
 (1
  1
  (:REWRITE
   ACL2PL::EVAL-STATE-INIT->FUNCTION$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST)))
(ACL2PL::EVAL-STATE-INIT->ARGUMENTS-OF-EVAL-STATE-INIT
 (1
  1
  (:REWRITE
   ACL2PL::EVAL-STATE-INIT->ARGUMENTS$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST)))
(ACL2PL::EVAL-STATE-INIT-OF-FIELDS
 (4 4
    (:REWRITE
         ACL2PL::EVAL-STATE-KIND$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST))
 (3 1
    (:REWRITE ACL2PL::EVAL-STATE-FIX-WHEN-EVAL-STATE-P))
 (2 2
    (:TYPE-PRESCRIPTION ACL2PL::EVAL-STATE-P))
 (1
  1
  (:REWRITE
   ACL2PL::EVAL-STATE-INIT->FUNCTION$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST))
 (1
  1
  (:REWRITE
   ACL2PL::EVAL-STATE-INIT->ARGUMENTS$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST)))
(ACL2PL::EVAL-STATE-FIX-WHEN-INIT
 (4 4
    (:REWRITE
         ACL2PL::EVAL-STATE-KIND$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST))
 (3 1
    (:REWRITE ACL2PL::EVAL-STATE-FIX-WHEN-EVAL-STATE-P))
 (2 2
    (:TYPE-PRESCRIPTION ACL2PL::EVAL-STATE-P))
 (1
  1
  (:REWRITE
   ACL2PL::EVAL-STATE-INIT->FUNCTION$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST))
 (1
  1
  (:REWRITE
   ACL2PL::EVAL-STATE-INIT->ARGUMENTS$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST)))
(ACL2PL::EQUAL-OF-EVAL-STATE-INIT
 (9
  9
  (:REWRITE
   ACL2PL::EVAL-STATE-INIT->FUNCTION$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST))
 (9
  9
  (:REWRITE
   ACL2PL::EVAL-STATE-INIT->ARGUMENTS$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST))
 (6
   6
   (:REWRITE
        ACL2PL::EVAL-STATE-KIND$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST)))
(ACL2PL::EVAL-STATE-INIT-OF-SYMBOL-VALUE-FIX-FUNCTION
     (4 2
        (:REWRITE ACL2PL::VALUE-LIST-FIX-WHEN-VALUE-LISTP))
     (2 2
        (:TYPE-PRESCRIPTION ACL2PL::VALUE-LISTP)))
(ACL2PL::EVAL-STATE-INIT-OF-SYMBOL-VALUE-FIX-FUNCTION-NORMALIZE-CONST)
(ACL2PL::EVAL-STATE-INIT-SYMBOL-VALUE-EQUIV-CONGRUENCE-ON-FUNCTION)
(ACL2PL::EVAL-STATE-INIT-OF-VALUE-LIST-FIX-ARGUMENTS
     (4 2
        (:REWRITE ACL2PL::SYMBOL-VALUE-FIX-WHEN-SYMBOL-VALUEP))
     (2 2
        (:TYPE-PRESCRIPTION ACL2PL::SYMBOL-VALUEP)))
(ACL2PL::EVAL-STATE-INIT-OF-VALUE-LIST-FIX-ARGUMENTS-NORMALIZE-CONST)
(ACL2PL::EVAL-STATE-INIT-VALUE-LIST-EQUIV-CONGRUENCE-ON-ARGUMENTS)
(ACL2PL::EVAL-STATE-TRANS->STACK$INLINE
 (2
   2
   (:REWRITE
        ACL2PL::EVAL-STATE-KIND$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST)))
(ACL2PL::STACKP-OF-EVAL-STATE-TRANS->STACK
 (3 1
    (:REWRITE ACL2PL::STACK-FIX-WHEN-STACKP))
 (1
   1
   (:REWRITE
        ACL2PL::EVAL-STATE-KIND$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST)))
(ACL2PL::EVAL-STATE-TRANS->STACK$INLINE-OF-EVAL-STATE-FIX-X
 (12 4
     (:REWRITE ACL2PL::EVAL-STATE-FIX-WHEN-EVAL-STATE-P))
 (8 8
    (:TYPE-PRESCRIPTION ACL2PL::EVAL-STATE-P))
 (7
   7
   (:REWRITE
        ACL2PL::EVAL-STATE-KIND$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST)))
(ACL2PL::EVAL-STATE-TRANS->STACK$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST)
(ACL2PL::EVAL-STATE-TRANS->STACK$INLINE-EVAL-STATE-EQUIV-CONGRUENCE-ON-X)
(ACL2PL::EVAL-STATE-TRANS->STACK-WHEN-WRONG-KIND
 (6 2
    (:REWRITE ACL2PL::STACK-FIX-WHEN-STACKP))
 (4 4 (:TYPE-PRESCRIPTION ACL2PL::STACKP))
 (2 2
    (:REWRITE
         ACL2PL::EVAL-STATE-KIND$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST))
 (1
  1
  (:REWRITE
   ACL2PL::EVAL-STATE-TRANS->STACK$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST)))
(ACL2PL::EVAL-STATE-TRANS)
(ACL2PL::RETURN-TYPE-OF-EVAL-STATE-TRANS
 (3 1
    (:REWRITE ACL2PL::STACK-FIX-WHEN-STACKP))
 (2 2 (:TYPE-PRESCRIPTION ACL2PL::STACKP))
 (1
   1
   (:REWRITE
        ACL2PL::EVAL-STATE-KIND$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST)))
(ACL2PL::EVAL-STATE-TRANS->STACK-OF-EVAL-STATE-TRANS
 (1
  1
  (:REWRITE
   ACL2PL::EVAL-STATE-TRANS->STACK$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST)))
(ACL2PL::EVAL-STATE-TRANS-OF-FIELDS
 (3 3
    (:REWRITE
         ACL2PL::EVAL-STATE-KIND$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST))
 (3 1
    (:REWRITE ACL2PL::EVAL-STATE-FIX-WHEN-EVAL-STATE-P))
 (2 2
    (:TYPE-PRESCRIPTION ACL2PL::EVAL-STATE-P))
 (1
  1
  (:REWRITE
   ACL2PL::EVAL-STATE-TRANS->STACK$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST)))
(ACL2PL::EVAL-STATE-FIX-WHEN-TRANS
 (3 3
    (:REWRITE
         ACL2PL::EVAL-STATE-KIND$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST))
 (3 1
    (:REWRITE ACL2PL::EVAL-STATE-FIX-WHEN-EVAL-STATE-P))
 (2 2
    (:TYPE-PRESCRIPTION ACL2PL::EVAL-STATE-P))
 (1
  1
  (:REWRITE
   ACL2PL::EVAL-STATE-TRANS->STACK$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST)))
(ACL2PL::EQUAL-OF-EVAL-STATE-TRANS
 (9
  9
  (:REWRITE
   ACL2PL::EVAL-STATE-TRANS->STACK$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST))
 (6
   6
   (:REWRITE
        ACL2PL::EVAL-STATE-KIND$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST)))
(ACL2PL::EVAL-STATE-TRANS-OF-STACK-FIX-STACK)
(ACL2PL::EVAL-STATE-TRANS-OF-STACK-FIX-STACK-NORMALIZE-CONST)
(ACL2PL::EVAL-STATE-TRANS-STACK-EQUIV-CONGRUENCE-ON-STACK)
(ACL2PL::EVAL-STATE-FINAL->RESULT$INLINE
 (2
   2
   (:REWRITE
        ACL2PL::EVAL-STATE-KIND$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST)))
(ACL2PL::VALUEP-OF-EVAL-STATE-FINAL->RESULT
 (3 1
    (:REWRITE ACL2PL::VALUE-FIX-WHEN-VALUEP))
 (1
   1
   (:REWRITE
        ACL2PL::EVAL-STATE-KIND$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST)))
(ACL2PL::EVAL-STATE-FINAL->RESULT$INLINE-OF-EVAL-STATE-FIX-X
 (12 4
     (:REWRITE ACL2PL::EVAL-STATE-FIX-WHEN-EVAL-STATE-P))
 (8 8
    (:TYPE-PRESCRIPTION ACL2PL::EVAL-STATE-P))
 (7
   7
   (:REWRITE
        ACL2PL::EVAL-STATE-KIND$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST)))
(ACL2PL::EVAL-STATE-FINAL->RESULT$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST)
(ACL2PL::EVAL-STATE-FINAL->RESULT$INLINE-EVAL-STATE-EQUIV-CONGRUENCE-ON-X)
(ACL2PL::EVAL-STATE-FINAL->RESULT-WHEN-WRONG-KIND
 (6 2
    (:REWRITE ACL2PL::VALUE-FIX-WHEN-VALUEP))
 (4 4 (:TYPE-PRESCRIPTION ACL2PL::VALUEP))
 (2 2
    (:REWRITE
         ACL2PL::EVAL-STATE-KIND$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST))
 (1
  1
  (:REWRITE
   ACL2PL::EVAL-STATE-FINAL->RESULT$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST)))
(ACL2PL::EVAL-STATE-FINAL)
(ACL2PL::RETURN-TYPE-OF-EVAL-STATE-FINAL
 (3 1
    (:REWRITE ACL2PL::VALUE-FIX-WHEN-VALUEP))
 (2 2 (:TYPE-PRESCRIPTION ACL2PL::VALUEP))
 (1
   1
   (:REWRITE
        ACL2PL::EVAL-STATE-KIND$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST)))
(ACL2PL::EVAL-STATE-FINAL->RESULT-OF-EVAL-STATE-FINAL
 (1
  1
  (:REWRITE
   ACL2PL::EVAL-STATE-FINAL->RESULT$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST)))
(ACL2PL::EVAL-STATE-FINAL-OF-FIELDS
 (3 3
    (:REWRITE
         ACL2PL::EVAL-STATE-KIND$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST))
 (3 1
    (:REWRITE ACL2PL::EVAL-STATE-FIX-WHEN-EVAL-STATE-P))
 (2 2
    (:TYPE-PRESCRIPTION ACL2PL::EVAL-STATE-P))
 (1
  1
  (:REWRITE
   ACL2PL::EVAL-STATE-FINAL->RESULT$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST)))
(ACL2PL::EVAL-STATE-FIX-WHEN-FINAL
 (3 3
    (:REWRITE
         ACL2PL::EVAL-STATE-KIND$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST))
 (3 1
    (:REWRITE ACL2PL::EVAL-STATE-FIX-WHEN-EVAL-STATE-P))
 (2 2
    (:TYPE-PRESCRIPTION ACL2PL::EVAL-STATE-P))
 (1
  1
  (:REWRITE
   ACL2PL::EVAL-STATE-FINAL->RESULT$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST)))
(ACL2PL::EQUAL-OF-EVAL-STATE-FINAL
 (9
  9
  (:REWRITE
   ACL2PL::EVAL-STATE-FINAL->RESULT$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST))
 (6
   6
   (:REWRITE
        ACL2PL::EVAL-STATE-KIND$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST)))
(ACL2PL::EVAL-STATE-FINAL-OF-VALUE-FIX-RESULT)
(ACL2PL::EVAL-STATE-FINAL-OF-VALUE-FIX-RESULT-NORMALIZE-CONST)
(ACL2PL::EVAL-STATE-FINAL-VALUE-EQUIV-CONGRUENCE-ON-RESULT)
(ACL2PL::EVAL-STATE-ERROR)
(ACL2PL::RETURN-TYPE-OF-EVAL-STATE-ERROR)
(ACL2PL::EVAL-STATE-FIX-WHEN-ERROR
 (3 1
    (:REWRITE ACL2PL::EVAL-STATE-FIX-WHEN-EVAL-STATE-P))
 (2 2
    (:TYPE-PRESCRIPTION ACL2PL::EVAL-STATE-P))
 (2
   2
   (:REWRITE
        ACL2PL::EVAL-STATE-KIND$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST)))
(ACL2PL::EQUAL-OF-EVAL-STATE-ERROR
 (3
   3
   (:REWRITE
        ACL2PL::EVAL-STATE-KIND$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST)))
(ACL2PL::EVAL-STATE-FIX-REDEF
 (12 4
     (:REWRITE ACL2PL::EVAL-STATE-FIX-WHEN-EVAL-STATE-P))
 (8 8
    (:TYPE-PRESCRIPTION ACL2PL::EVAL-STATE-P))
 (5 5
    (:REWRITE
         ACL2PL::EVAL-STATE-KIND$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST))
 (1 1
    (:REWRITE ACL2PL::EVAL-STATE-TRANS-OF-STACK-FIX-STACK-NORMALIZE-CONST))
 (1
  1
  (:REWRITE
   ACL2PL::EVAL-STATE-TRANS->STACK$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST))
 (1
   1
   (:REWRITE
        ACL2PL::EVAL-STATE-INIT-OF-VALUE-LIST-FIX-ARGUMENTS-NORMALIZE-CONST))
 (1
  1
  (:REWRITE
       ACL2PL::EVAL-STATE-INIT-OF-SYMBOL-VALUE-FIX-FUNCTION-NORMALIZE-CONST))
 (1
  1
  (:REWRITE
   ACL2PL::EVAL-STATE-INIT->FUNCTION$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST))
 (1
  1
  (:REWRITE
   ACL2PL::EVAL-STATE-INIT->ARGUMENTS$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST))
 (1 1
    (:REWRITE ACL2PL::EVAL-STATE-FINAL-OF-VALUE-FIX-RESULT-NORMALIZE-CONST))
 (1
  1
  (:REWRITE
   ACL2PL::EVAL-STATE-FINAL->RESULT$INLINE-OF-EVAL-STATE-FIX-X-NORMALIZE-CONST)))
