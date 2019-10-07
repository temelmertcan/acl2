; RP-REWRITER

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2019, Regents of the University of Texas
; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Mertcan Temel         <mert@utexas.edu>

(in-package "RP")

(include-book "../rp-rewriter")
(include-book "match-lhs-lemmas")
(include-book "rp-equal-lemmas")
(include-book "apply-bindings-lemmas")
;(include-book "falist-lemmas")
(include-book "apply-meta-lemmas")
(include-book "ex-counterpart-lemmas")
(include-book "rp-state-functions-lemmas")

(local
 (in-theory
  (disable
   (:rewrite atom-pseudo-termp2-is-symbolp)
   hons-get
   rp-stat-add-to-rules-used
;is-exc-enabled
   rp-ex-counterpart
   (:definition len)
   (:definition rp-exc-all)
;(:definition rp-rw-apply-meta)
   (:definition rp-check-context)
   (:definition rp-ev-fncall)
   (:definition rp-apply-bindings)
   valid-rulep
   valid-rulesp
   valid-rules-alistp
   rp-rw-rule-aux
   is-rp
   (:DEFINITION RP-RW-META-RULES)
   (:DEFINITION RP-RW-META-RULE)
   is-synp
   ex-from-rp
   rp-equal2
   EX-FROM-SYNP-LEMMA1
   rp-equal
   ex-from-rp-lemma1
   (:definition unquote-all)
   (:definition remove-rp-from-bindings)
   (:definition rp-extract-context)
   (:definition rp-get-dont-rw)
   (:definition rp-ex-counterpart)
   dumb-negate-lit2
   ex-from-rp
   (:definition rp-rw-relieve-synp)
   (:definition quote-listp)

   RP-DONT-RW$INLINE
   RP-DONT-RW-SIZE$INLINE
   RP-HYP-DONT-RW$INLINE)))

(set-state-ok t)
(with-output
  :off :all
  :on error
  :gag-mode nil
  (make-flag rp-rw :defthm-macro-name defthm-rp-rw
             :hints
             (("Goal"
               :in-theory
               (disable QUOTEP
                        (:DEFINITION RP-CHECK-CONTEXT)
                        (:DEFINITION LEN)

                        (:REWRITE DEFAULT-<-1)
                        (:REWRITE DEFAULT-<-2)

                        (:DEFINITION RP-RW-RELIEVE-SYNP)
                        (:TYPE-PRESCRIPTION quote-listp)
                        (:TYPE-PRESCRIPTION IS-IF$inline)
                        (:DEFINITION RP-RW-RELIEVE-SYNP)
                        (:DEFINITION RP-EXC-ALL)
                        (:TYPE-PRESCRIPTION O<)
                        (:TYPE-PRESCRIPTION QUOTEP)
                        (:TYPE-PRESCRIPTION RETURN-LAST)
                        (:DEFINITION RP-RW-META-RULES)
                        (:DEFINITION RP-RW-META-RULE)
                        (:REWRITE DEFAULT-+-2)
                        (:REWRITE DEFAULT-+-1)
;(:DEFINITION O<)
                        (:DEFINITION RETURN-LAST)
;(:DEFINITION O-FINP)
                        (:TYPE-PRESCRIPTION RP-RW-RELIEVE-SYNP)
                        (:TYPE-PRESCRIPTION NONNIL-P)
                        (:DEFINITION HONS-ASSOC-EQUAL)
                        (:DEFINITION RP-APPLY-BINDINGS)
                        (:DEFINITION REMOVE-RP-FROM-BINDINGS)
                        EX-FROM-RP
                        #|RESOLVE-ASSOC-EQ-VALS||#
; RESOLVE-PP-SUM-ORDER
                        quote-listp
                        IS-NONNIL-FIX
                        nonnil-fix
;is-exc-enabled
                        dont-rw-if-fix

                        RP-EX-COUNTERPART
;RP-RW-APPLY-META
                        rp-rw-rule-aux
                        UPDATE-NTH)))))

(local
 (in-theory (disable context-syntaxp)))

(local
 (defthmd context-syntaxp-def
   (equal (context-syntaxp context)
          (AND (PSEUDO-TERM-LISTP2 CONTEXT)
               (rp-syntaxp-lst context)
               (ALL-FALIST-CONSISTENT-LST CONTEXT)))
   :hints (("Goal"
            :in-theory (e/d (context-syntaxp) ())))))

(defthm return-val-of-rp-extract-context
  (implies (and (pseudo-termp2 term)
                (rp-syntaxp term)
                (all-falist-consistent term))
           (context-syntaxp (rp-extract-context term)))
  :hints (("Goal" :in-theory (enable rp-extract-context
                                     append
                                     all-falist-consistent
                                     all-falist-consistent-lst
                                     is-falist
                                     pseudo-term-listp2
                                     context-syntaxp-def
                                     ))))

#|(local
 (defthm lemma1
   (implies (valid-sc term a)
            (VALID-SC (CADDR TERM) A))
   :hints (("Goal"
            :expand ((valid-sc term a))
            :in-theory (e/d () ())))))||#

(defthm extract-context-is-valid-sc
  (implies (and (valid-sc term a)
                (rp-evl term a))
           (valid-sc-subterms (RP-EXTRACT-CONTEXT term) a))
  :hints (("Goal"
           :in-theory (e/d (rp-extract-context
                            is-if
                            valid-sc-subterms
                            valid-sc) ()))))

(defthm pseudo-termp2-rp-check-context
  (implies (and (context-syntaxp context)
                (pseudo-termp2 term))
           (PSEUDO-TERMP2 (mv-nth 0 (RP-CHECK-CONTEXT TERM dont-rw CONTEXT IFF-FLG))))
  :hints (("Goal" :in-theory (e/d
                              (pseudo-termp2
                               context-syntaxp
                               pseudo-termp2
                               pseudo-term-listp2
                               rp-check-context)
                              ((:DEFINITION RP-SYNTAXP)
                               (:DEFINITION ALL-FALIST-CONSISTENT)
                               (:REWRITE RP-EQUAL-IS-SYMMETRIC)
;(:DEFINITION RP-SYNTAXP-LST)
;(:DEFINITION RP-SYNTAXP-LST)
;(:DEFINITION ALL-FALIST-CONSISTENT-LST)
                               (:DEFINITION ACL2::APPLY$-BADGEP)
                               (:REWRITE PSEUDO-TERMP2-IMPLIES-CDR-LISTP)
                               (:DEFINITION TRUE-LISTP)

                               (:REWRITE NOT-INCLUDE-RP-MEANS-RP-SYNTAXP-LST)
                               (:DEFINITION INCLUDE-FNC-SUBTERMS)
                               )))))

(defthm rp-syntaxp-rp-check-context
  (implies (and (rp-syntaxp term)
                (context-syntaxp context))
           (rp-syntaxp (mv-nth 0 (rp-check-context term dont-rw context iff-flg))))
  :hints (("Goal"
           :in-theory (e/d (context-syntaxp
                            rp-check-context)
                           ((:DEFINITION PSEUDO-TERMP2)
                            (:DEFINITION IS-FALIST)
                            (:DEFINITION ALL-FALIST-CONSISTENT)
                            (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                            (:DEFINITION ACL2::APPLY$-BADGEP)
                            (:DEFINITION SUBSETP-EQUAL)
                            (:REWRITE
                             ALL-FALIST-CONSISTENT-LST-CDR-TERM-LEMMA)
;(:DEFINITION PSEUDO-TERM-LISTP2)
                            )))))

(defthm remove-rp-from-bindings-is-bindings
  (implies (bindings-alistp bindings)
           (bindings-alistp (remove-rp-from-bindings bindings)))
  :hints (("goal"
           :in-theory (enable remove-rp-from-bindings))))

(defthm rp-syntaxp-bindings-remove-rp-from-bindings
  (implies (rp-syntaxp-bindings bindings)
           (rp-syntaxp-bindings (remove-rp-from-bindings bindings)))
  :hints (("goal"
           :in-theory (e/d (remove-rp-from-bindings) ()))))

(defthm rp-get-rules-for-term-returns-rule-list-syntaxp
  (implies (rules-alistp rules-alist)
           (rule-list-syntaxp (rp-get-rules-for-term fn rules-alist)))
  :hints (("goal" :in-theory (enable hons-get hons-assoc-equal
                                     rules-alistp))))

(defthm valid-falist-rp-check-context
  (implies (and (all-falist-consistent term)
                (all-falist-consistent-lst context))
           (all-falist-consistent (mv-nth 0 (rp-check-context term dont-rw context iff-flg))))
  :hints (("goal" :in-theory (e/d (rp-check-context)
                                  ((:definition acl2::apply$-badgep)
                                   (:linear acl2::apply$-badgep-properties . 1)
                                   (:rewrite pseudo-term-listp2-is-true-listp)
                                   (:rewrite
                                    cdr-term-is-all-falist-consistent-lst)
                                   (:definition true-listp)
                                   (:rewrite acl2::o-p-o-infp-car))))))

(defthm pseudo-term-listp2-rp-extract-context
  (implies (pseudo-termp2 term)
           (pseudo-term-listp2 (rp-extract-context term)))
  :hints (("goal" :in-theory (enable rp-extract-context pseudo-term-listp2
                                     pseudo-termp2))))

(defthm all-falist-consistent-lst-rp-extract-context
  (implies (all-falist-consistent term)
           (all-falist-consistent-lst (rp-extract-context term)))
  :hints (("goal" :in-theory (enable rp-extract-context
                                     all-falist-consistent-lst
                                     all-falist-consistent
                                     pseudo-term-listp2
                                     pseudo-termp2))))

(defthm all-falist-consistent-dumb-negate-lit2
  (implies (all-falist-consistent term)
           (all-falist-consistent (dumb-negate-lit2 term)))
  :hints (("goal" :in-theory (enable dumb-negate-lit2
                                     is-falist
                                     all-falist-consistent))))

(defthm rp-syntaxp-dumb-negate-lit2
  (implies (rp-syntaxp term)
           (rp-syntaxp (dumb-negate-lit2 term)))
  :hints (("Goal" :in-theory (enable dumb-negate-lit2
                                     is-rp
                                     rp-syntaxp))))

(defthm rp-rule-is-applicable-not-iff
  ;; when a valid rule is applied on a term with good bindings,
  ;; the rhs of applied rule should be the same as the term.
  (implies (and (rp-evl (rp-apply-bindings (rp-hyp rule) bindings) a)
                (pseudo-termp2 term)
                (good-bindingsp rule term bindings a)
                (bindings-alistp bindings)
                (valid-rulep rule)
                (alistp a)
                (pseudo-termp2 (rp-rhs rule))
                (not (rp-iff-flag rule)))
           (equal (rp-evl (rp-apply-bindings (rp-rhs rule) bindings) a)
                  (rp-evl term a)))
  :hints (("goal"
           :use ((:instance valid-rulep-sk-necc
                            (a (bind-bindings bindings a)))
                 (:instance rp-evl-of-rp-equal2
                            (term1 (rp-apply-bindings (rp-lhs rule) bindings))
                            (term2 term)
                            (a a)))
           :in-theory (e/d (valid-rulep
                            valid-rulesp
                            valid-rules-alistp)
                           (rp-evl-of-rp-equal
                            (:DEFINITION ALWAYS$)
                            (:DEFINITION SUBSETP-EQUAL)
                            (:DEFINITION MEMBER-EQUAL)
                            (:REWRITE PSEUDO-TERM-LISTP2-IS-TRUE-LISTP)
                            (:REWRITE ACL2::PLAIN-UQI-TRUE-LIST-LISTP)
                            (:DEFINITION PSEUDO-TERM-LISTP2)
                            (:DEFINITION TRUE-LISTP)
                            (:DEFINITION ACL2::APPLY$-BADGEP)
                            (:REWRITE
                             ACL2::TRUE-LIST-LISTP-IMPLIES-ALWAYS$-TRUE-LISTP)
                            (:DEFINITION TRUE-LIST-LISTP)
                            (:REWRITE ACL2::PLAIN-UQI-INTEGER-LISTP)
                            (:REWRITE ACL2::APPLY$-SYMBOL-ARITY-1)
                            (:REWRITE ACL2::APPLY$-PRIMITIVE)
                            (:REWRITE RP-APPLY-BINDINGS-EQUIV-NOT-IFF)
                            (:DEFINITION BIND-BINDINGS-AUX)
                            (:REWRITE VALID-RULEP-IMPLIES-VALID-SC)
                            (:TYPE-PRESCRIPTION EX-FROM-SYNP)
                            (:TYPE-PRESCRIPTION INCLUDE-FNC-SUBTERMS)
                            valid-rulep-sk-necc
                            ;;rp-equal-of-two-2
                            rp-equal-is-symmetric
                            pseudo-termp  rp-lhs rp-rhs pseudo-termp2
                            rp-hyp)))))

(defthm rp-rule-is-applicable-iff
  ;; when a valid rule is applied on a term with good bindings,
  ;; the rhs of applied rule should be the same as the term.
  (implies (and (rp-evl (rp-apply-bindings (rp-hyp rule) bindings) a)
                (pseudo-termp2 term)
                (good-bindingsp rule term bindings a)
                (bindings-alistp bindings)
                (valid-rulep rule)
                (alistp a)
                (pseudo-termp2 (rp-rhs rule)))
           (iff (rp-evl (rp-apply-bindings (rp-rhs rule) bindings) a)
                (rp-evl term a))
           #|(rp-evl term a)||#)
  :hints (("goal"
           :use ((:instance valid-rulep-sk-necc
                            (a (bind-bindings bindings a)))
                 (:instance rp-evl-of-rp-equal2
                            (term1 (rp-apply-bindings (rp-lhs rule) bindings))
                            (term2 term)
                            (a a)))
           :in-theory (e/d (valid-rulep
                            valid-rulesp
                            valid-rules-alistp)
                           (rp-evl-of-rp-equal
                            (:DEFINITION GET-VARS1)
                            (:REWRITE ACL2::APPLY$-PRIMITIVE)
                            rp-evl-of-rp-equal2
                            RP-EQUAL2-IS-symmetric
                            rp-rule-is-applicable-not-iff
                            (:REWRITE RP-APPLY-BINDINGS-EQUIV-NOT-IFF)
                            (:DEFINITION BIND-BINDINGS-AUX)
                            (:REWRITE VALID-RULEP-IMPLIES-VALID-SC)
                            (:TYPE-PRESCRIPTION EX-FROM-SYNP)
                            (:TYPE-PRESCRIPTION INCLUDE-FNC-SUBTERMS)
                            (:DEFINITION RP-SYNTAXP)
                            (:DEFINITION EVAL-AND-ALL)
                            (:REWRITE VALID-SC-CONS)
                            (:DEFINITION SUBSETP-EQUAL)
                            (:REWRITE NOT-INCLUDE-RP)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-VALID-SC)
                            (:REWRITE RP-EVL-OF-VARIABLE)
                            (:REWRITE RP-EVL-OF-UNARY-/-CALL)
                            (:REWRITE RP-EVL-OF-UNARY---CALL)
                            (:REWRITE RP-EVL-OF-TYPESPEC-CHECK-CALL)
                            (:REWRITE EVL-OF-EXTRACT-FROM-RP-2)
                            (:TYPE-PRESCRIPTION BIND-BINDINGS-AUX)
                            valid-rulep-sk-necc
                            ;;rp-equal-of-two-2
                            rp-equal-is-symmetric
                            pseudo-termp  rp-lhs rp-rhs pseudo-termp2
                            rp-hyp)))))

(make-flag rp-get-dont-rw :defthm-macro-name defthm-rp-get-dont-rw)

#|(defthm-rp-get-dont-rw

  (defthm dont-rw-syntaxp-rp-get-dont-rw
    (dont-rw-syntaxp (rp-get-dont-rw term))
    :flag rp-get-dont-rw)

  (defthm dont-rw-syntaxp-rp-get-dont-rw-subterms
    (dont-rw-syntaxp (rp-get-dont-rw-subterm subterm))
    :flag rp-get-dont-rw-subterm)
  :hints (("Goal"
           :in-theory (e/d (DONT-RW-SYNTAXP
                            DONT-RW-SYNTAXP-AUX
                            RP-GET-DONT-RW-SUBTERM
                            rp-get-dont-rw) ()))))||#

(defthm natp-rp-check-context
  (implies (natp dont-rw)
           (natp (mv-nth 1 (rp-check-context term dont-rw context iff-flg))))
  :rule-classes :type-prescription
  :hints (("Goal"
           :in-theory (e/d (rp-check-context)
                           (natp)))))

#|(with-output
  :off (warning event  prove  observation)
  :gag-mode :goals
  :on error
  (defthm dont-rw-syntaxp-rp-rw-rule
    (implies (equal flag 'rp-rw-rule)
             (dont-rw-syntaxp
              (mv-nth 2 (rp-rw-rule term rules-for-term context limit rules-alist exc-rules
                                    meta-rules iff-flg rp-state state))))
    :hints (("Goal"
             :induct (FLAG-RP-RW flag RULES-FOR-TERM
                                 TERM IFF-FLG SUBTERMS DONT-RW CONTEXT
                                 LIMIT RULES-ALIST EXC-RULES meta-rules rp-state STATE)
             #| :induct (rp-rw-rule term rules-for-term context limit rules-alist exc-rules
             iff-flg stat state)||#
             :in-theory (e/d (rp-rw-rule
                              (:INDUCTION RP-RW-RULE))
                             (remove-rp-from-bindings
                              rp-rw-relieve-synp
                              rp-rw-rule-aux
                              rp-apply-bindings))))))||#

(defthm rp-get-rules-for-term-returns-valid-rulesp
  (implies (valid-rules-alistp rules-alist)
           (valid-rulesp (rp-get-rules-for-term fn-name rules-alist)))
  :hints (("Goal" :in-theory (enable valid-rulesp
                                     hons-get
                                     hons-assoc-equal
                                     valid-rules-alistp))))

(defthm rp-check-context-is-correct-iff
  (implies
   (and (pseudo-termp2 term)
        (rp-syntaxp term)
        (valid-sc term a)
        (context-syntaxp context)
        iff-flg
        (eval-and-all context a))
   (iff (rp-evl (mv-nth 0 (rp-check-context term dont-rw context iff-flg)) a)
        (rp-evl term a)))
  :hints (("Subgoal *1/2"
           :use ((:instance rp-evl-of-rp-equal
                            (term1 term)
                            (term2 (CADR (CAR CONTEXT))))))
          ("Subgoal *1/3"
           :use ((:instance rp-evl-of-rp-equal
                            (term1 (car context))
                            (term2 term))))
          ("Goal"
           :in-theory (e/d (rp-check-context
                            is-rp
                            is-if
                            CONTEXT-SYNTAXP
                            pseudo-termp2
                            eval-and-all)
                           (PSEUDO-TERM-LISTP2-IS-TRUE-LISTP
                            ALL-FALIST-CONSISTENT
                            (:DEFINITION ACL2::APPLY$-BADGEP)
                            (:REWRITE ACL2::APPLY$-BADGEP-PROPERTIES . 3)
                            (:DEFINITION SUBSETP-EQUAL)
                            (:DEFINITION MEMBER-EQUAL)
                            (:REWRITE ACL2::O-P-O-INFP-CAR)
                            (:REWRITE
                             ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1)
                            (:TYPE-PRESCRIPTION MEMBER-EQUAL)
                            (:DEFINITION NATP)
                            (:REWRITE
                             ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-3)
                            (:REWRITE RP-SYNTAXP-CADR)
                            (:TYPE-PRESCRIPTION NATP)
                            (:TYPE-PRESCRIPTION
                             NATP-CUT-DONT-RW-WITH-TERM-LST)
                            (:TYPE-PRESCRIPTION
                             NATP-CUT-DONT-RW-WITH-TERM)
                            rp-evl-of-rp-equal
                            (:REWRITE EX-FROM-SYNP-LEMMA1)
                            (:REWRITE NOT-INCLUDE-RP-MEANS-RP-SYNTAXP-LST)
                            (:REWRITE
                             NOT-INCLUDE-FALIST-ALL-FALIST-CONSISTENT-LST)
                            (:REWRITE
                             ALL-FALIST-CONSISTENT-LST-CDR-TERM-LEMMA)
                            (:REWRITE EVL-OF-EXTRACT-FROM-RP-2)
                            (:REWRITE ACL2::FN-CHECK-DEF-NOT-QUOTE)
                            (:REWRITE
                             CDR-TERM-IS-ALL-FALIST-CONSISTENT-LST)
                            (:REWRITE
                             PSEUDO-TERMP2-SHOULD-TERM-BE-IN-CONS-LHS)
                            (:TYPE-PRESCRIPTION BOOLEANP)
                            (:REWRITE RP-EQUAL2-BINDINGS-1TO1-CONSP)
                            ;;ALL-FALIST-CONSISTENT-LST
                            falist-consistent
                            IS-FALIST
                            PSEUDO-TERMP2-IMPLIES-SUBTERMS)))))

(local
 (in-theory (disable  (:DEFINITION ACL2::APPLY$-BADGEP)
                      (:REWRITE ACL2::APPLY$-BADGEP-PROPERTIES . 3))))

(defthm rp-check-context-is-correct-not-iff
  (implies
   (and (pseudo-termp2 term)
        (valid-sc term a)
        (rp-syntaxp term)
        (context-syntaxp context)
        (eval-and-all context a))
   (equal (rp-evl (mv-nth 0 (rp-check-context term dont-rw context nil)) a)
          (rp-evl term a)))
  :hints (("Goal"
           :in-theory (e/d (rp-check-context
                            CONTEXT-SYNTAXP
                            pseudo-termp2
                            eval-and-all)
                           (PSEUDO-TERM-LISTP2-IS-TRUE-LISTP
                            ALL-FALIST-CONSISTENT
                            (:REWRITE EX-FROM-SYNP-LEMMA1)
                            (:REWRITE RP-EQUAL2-BINDINGS-1TO1-CONSP)
                            (:DEFINITION SUBSETP-EQUAL)
                            (:DEFINITION MEMBER-EQUAL)
                            (:REWRITE PSEUDO-TERMP2-IMPLIES-CDR-LISTP)
                            (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                            (:REWRITE ACL2::O-P-O-INFP-CAR)
                            (:TYPE-PRESCRIPTION INCLUDE-FNC-SUBTERMS)
                            (:DEFINITION VALID-SC)
;ALL-FALIST-CONSISTENT-LST
                            falist-consistent
                            IS-FALIST
                            PSEUDO-TERMP2-IMPLIES-SUBTERMS)))))

(defthm VALID-SC-BINDINGS-REMOVE-RP-FROM-BINDINGS
  (implies (valid-sc-bindings bindings a)
           (valid-sc-bindings (REMOVE-RP-FROM-BINDINGS bindings) a))
  :hints (("Goal"
           :in-theory (e/d (valid-sc-bindings
                            remove-rp-from-bindings) ()))))

(encapsulate
  nil

  (local
   (in-theory (enable is-rp-implies-fc)))

  (local
   (defthm lemma1-lemma0
     (IMPLIES (AND (IS-RP TERM)
                   (EVAL-AND-ALL (CONTEXT-FROM-RP TERM NIL)
                                 A)
                   (PSEUDO-TERM-LISTP2 (CDR TERM))
                   (RP-SYNTAXP TERM))
              (RP-EVL (LIST (CADR (CADR TERM)) TERM)
                      A))
     :hints (("Goal"
              :expand ((CONTEXT-FROM-RP TERM NIL))
              :in-theory (e/d (EVAL-AND-ALL
                               is-rp
                               rp-evl-of-fncall-args)
                              (EX-FROM-RP-LEMMA1))))))

  (local
   (defthm lemma1-lemma1
     (IMPLIES (AND (IS-RP TERM)
                   (not (equal fnc 'quote))
                   (RP-EVL (LIST FNC (CADDR TERM)) A)
                   (PSEUDO-TERMP2 (CADDR TERM))
                   (RP-SYNTAXP (CADDR TERM)))
              (RP-EVL (LIST FNC TERM) A))
     :hints (("Goal"
              :expand ((CONTEXT-FROM-RP TERM NIL))
              :in-theory (e/d (EVAL-AND-ALL
                               is-rp
                               rp-evl-of-fncall-args)
                              (EX-FROM-RP-LEMMA1))))))

  (local
   (defthm lemma1
     (implies (and (EVAL-AND-ALL (CONTEXT-FROM-RP term NIL) A)
                   (pseudo-termp2 term)
                   (not (equal fnc 'quote))
                   (rp-syntaxp term)
                   (check-if-relieved-with-rp-aux fnc term))
              (rp-evl `(,fnc ,term) a))
     :otf-flg t
     :hints (("Goal"
              :induct (check-if-relieved-with-rp-aux fnc term)
              :in-theory (e/d (check-if-relieved-with-rp-aux
; is-rp
                               eval-and-all
                               context-from-rp
                               quotep
                               )
                              (ex-from-rp-lemma1))))))

  (defthm check-if-relieved-with-rp-is-correct
    (implies (and (check-if-relieved-with-rp term)
                  (valid-sc term a)
                  (rp-syntaxp term)
                  (pseudo-termp2 term))
             (rp-evl term a))
    :hints (("Goal"

             :in-theory (e/d (check-if-relieved-with-rp
                              is-if
                              is-rp
                              check-if-relieved-with-rp-aux) ())))))

(local
 (in-theory
  (disable
   rp-meta-valid-syntax-listp
   rp-rw-meta-rules
   valid-rp-meta-rule-listp

   rp-statep

   (:type-prescription rule-list-syntaxp)
   ;;(:type-prescription dont-rw-if-fix)
   (:definition strip-cars)
   ;;(:type-prescription remove-rp-from-bindings)
   ;;(:meta acl2::mv-nth-cons-meta)
   (:definition rp-rw-subterms)

   (:type-prescription context-syntaxp)
   (:rewrite default-<-1)
   (:type-prescription alistp)
   (:type-prescription true-list-listp)
   (:type-prescription eqlable-alistp)

   (:rewrite pseudo-term-listp2-is-true-listp)

   (:definition assoc-equal)

   (:rewrite acl2::zp-open)

   (:type-prescription is-rp$inline)

   (:rewrite acl2::append-when-not-consp)
   ;; (:type-prescription rp-extract-context)
   (:rewrite acl2::append-atom-under-list-equiv)

   (:type-prescription is-if$inline)
   (:type-prescription rules-alistp)
   (:type-prescription pseudo-term-listp2)
   (:type-prescription quote-listp)
   (:type-prescription quotep)

   (:type-prescription pseudo-termp2)
   (:definition falist-consistent)
   (:definition no-free-variablep)
   (:type-prescription rule-list-list-syntaxp)
   (:definition rule-list-syntaxp)
   (:definition rule-syntaxp)
   (:definition rule-list-list-syntaxp)
   (:rewrite rp-equal2-bindings-1to1-consp)
   (:definition get-vars)
   (:definition true-listp)
   (:definition include-fnc)
   (:definition subsetp-equal)
   (:rewrite
    pseudo-termp2-should-term-be-in-cons-lhs)
   (:definition hons-assoc-equal)
   (:definition symbol-listp)
   (:definition symbol-alistp)
   #|(:definition RP-RW-APPLY-FALIST-META)||#
   (:definition is-falist)
   (:definition strip-cdrs)
   (:type-prescription all-falist-consistent-lst)
   (:type-prescription all-falist-consistent)
   (:type-prescription is-falist)

   (:definition alistp)
   (:definition symbol-alistp)
   #|(:type-prescription rp-rw-apply-falist-meta)||#
   (:definition hons-get)
   (:definition rules-alistp)
   (:type-prescription falist-consistent)
   (:type-prescription true-listp)
   (:type-prescription zp)
   (:type-prescription hons-assoc-equal)
   (:type-prescription rp-rw-rule)
   (:type-prescription rp-ex-counterpart)
;(:type-prescription rp-rw-apply-meta)
   (:REWRITE DEFAULT-+-2)
   (:REWRITE DEFAULT-+-1)
   (:TYPE-PRESCRIPTION RP-EXTRACT-CONTEXT)
   (:DEFINITION BINARY-APPEND)
   (:TYPE-PRESCRIPTION acl2::TRUE-LISTP-APPEND)
   (:TYPE-PRESCRIPTION RP-META-VALID-SYNTAX-LISTP)
   (:REWRITE ACL2::CONSP-OF-APPEND)
   (:REWRITE ACL2::CAR-OF-APPEND)
   (:TYPE-PRESCRIPTION BINARY-APPEND)
   (:FORWARD-CHAINING
    SYMBOL-ALISTP-FORWARD-TO-EQLABLE-ALISTP)
   (:FORWARD-CHAINING
    EQLABLE-ALISTP-FORWARD-TO-ALISTP)
   (:FORWARD-CHAINING
    ALISTP-FORWARD-TO-TRUE-LISTP)
   (:TYPE-PRESCRIPTION RP-RW-RELIEVE-SYNP)
   dumb-negate-lit2
   rp-rw-if
   rp-rw-rule
   rp-rw
   iff
   is-falist
   IS-HONSED-ASSOC-EQ-VALUES
   #|RP-RW-APPLY-FALIST-META||#
;HONS-ACONS-META
;HONS-ACONS
   nonnil-p
   EX-AND-EVAL-SC
   EX-AND-EVAL-SC-SUBTERMS
   logapp
   acl2::logcdr
   (:REWRITE DEFAULT-*-2)
   (:REWRITE DEFAULT-*-1)
   acl2::logcar
   ;; (:meta acl2::mv-nth-cons-meta)
   (:type-prescription symbol-alistp))))

(encapsulate
  nil

  (local
   (in-theory (disable ACL2::CDR-OF-APPEND-WHEN-CONSP
                       RP-EQUAL
                       VALID-RULES-ALISTP-IMPLIES-RULES-ALISTP
                       PSEUDO-TERM-LISTP2-APPEND
                       RP-EXTRACT-CONTEXT
                       RP-RW-RULE-AUX
                       CDR-TERM-IS-ALL-FALIST-CONSISTENT-LST
                       IS-RP-PSEUDO-TERMP
                       IS-IF-PSEUDO-TERMP2
                       IS-IF-PSEUDO-TERMP2
                       (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT)
                       (:TYPE-PRESCRIPTION NATP-RP-CHECK-CONTEXT)

                       (:META ACL2::MV-NTH-CONS-META)
                       )))

  (with-output
    :off (warning event  prove  observation)
    :gag-mode nil
    :on error

    (defthm-rp-rw
      (defthm rp-rw-returns-valid-rp-statp
        (implies (rp-statep rp-state)
                 (rp-statep
                  (mv-nth 2 (rp-rw term
                                   dont-rw
                                   context limit
                                   rules-alist exc-rules
                                   meta-rules
                                   iff-flg rp-state
                                   state))))
        :flag rp-rw)
      (defthm rp-rw-rule-retuns-valid-rp-statp
        (implies (rp-statep rp-state)
                 (rp-statep
                  (mv-nth 3 (rp-rw-rule term dont-rw rules-for-term context limit rules-alist exc-rules
                                        meta-rules iff-flg rp-state state))))
        :flag rp-rw-rule)

      (defthm rp-rw-if-retuns-valid-rp-statp
        (implies (rp-statep rp-state)
                 (rp-statep
                  (mv-nth 2 (rp-rw-if term dont-rw context limit rules-alist
                                      exc-rules meta-rules
                                      iff-flg rp-state state))))
        :flag rp-rw-if)

      (defthm rp-rw-subterms-retuns-valid-rp-statp
        (implies (rp-statep rp-state)
                 (rp-statep
                  (mv-nth 2 (rp-rw-subterms subterms dont-rw context limit
                                            rules-alist exc-rules meta-rules
                                            rp-state state))))
        :flag rp-rw-subterms)

      :hints (("goal"
               :expand ((rp-rw-rule term dont-rw
                                    rules-for-term context limit rules-alist
                                    exc-rules meta-rules iff-flg rp-state state)
                        (rp-rw-if term dont-rw context limit rules-alist
                                  exc-rules meta-rules iff-flg rp-state state)
                        (rp-rw term 1 context limit rules-alist
                               exc-rules meta-rules iff-flg rp-state state)
                        (rp-rw term dont-rw context limit
                               rules-alist exc-rules meta-rules nil rp-state state)
                        (rp-rw term dont-rw context limit rules-alist
                               exc-rules meta-rules iff-flg rp-state state)
                        (rp-rw-subterms subterms dont-rw context limit
                                        rules-alist exc-rules meta-rules rp-state state))
               :in-theory (e/d (RP-STAT-ADD-TO-RULES-USED)
                               (update-rules-used
                                SHOW-USED-RULES-FLG
                                UPDATE-NTH
                                RP-STAT-ADD-TO-RULES-USED)))))))

(encapsulate
  nil

  (local
   (in-theory (disable ACL2::CDR-OF-APPEND-WHEN-CONSP
                       RP-EQUAL
                       VALID-RULES-ALISTP-IMPLIES-RULES-ALISTP
                       PSEUDO-TERM-LISTP2-APPEND
                       RP-EXTRACT-CONTEXT
                       RP-RW-RULE-AUX
                       (:REWRITE NOT-INCLUDE-RP-MEANS-RP-SYNTAXP-LST)
                       (:REWRITE
                        NOT-INCLUDE-FALIST-ALL-FALIST-CONSISTENT-LST)
                       (:REWRITE
                        ALL-FALIST-CONSISTENT-LST-CDR-TERM-LEMMA)
                       CDR-TERM-IS-ALL-FALIST-CONSISTENT-LST
                       IS-RP-PSEUDO-TERMP
                       IS-IF-PSEUDO-TERMP2
                       IS-IF-PSEUDO-TERMP2)))

  (local
   (in-theory (enable ;rp-rw
               ;;rp-rw-rule
               context-syntaxp
               rule-syntaxp-implies
               quotep)))

  (local
   (defthm lemma1
     (implies (and (consp term))
              (CONSP (MV-NTH 0
                             (RP-EX-COUNTERPART term
                                                EXC-RULES rp-state STATE))))
     :hints (("Goal" :in-theory (enable rp-ex-counterpart)))))

  (local
   (defthm lemma2
     (implies (and (pseudo-term-listp2 subterms))
              (pseudo-termp2 (cons 'hide subterms)))
     :hints (("Goal"
              :in-theory (enable pseudo-term-listp2 pseudo-termp2 true-listp)
              :expand (pseudo-termp2 (cons 'hide subterms))))))

  (local
   (defthm lemma3
     (implies (and (all-falist-consistent-lst subterms))
              (all-falist-consistent (cons 'hide subterms)))
     :hints (("Goal"
              :in-theory (enable is-falist all-falist-consistent-lst all-falist-consistent true-listp)
              :expand (all-falist-consistent (cons 'hide subterms))))))

  (local
   (defthm lemma6
     (implies (and (consp term)
                   (not (equal (car term) 'falist))
                   (ALL-FALIST-CONSISTENT-lst subterms))
              (ALL-FALIST-CONSISTENT (cons (car term) subterms)))
     :otf-flg t
     :hints (("Goal"
              :expand ((ALL-FALIST-CONSISTENT (CONS (CAR TERM) SUBTERMS)))
              :in-theory (enable true-listp
                                 FALIST-CONSISTENT
                                 is-falist
                                 ALL-FALIST-CONSISTENT-lst
                                 ALL-FALIST-CONSISTENT-lst
                                 pseudo-term-listp2)))))

  (local
   (defthm lemma7
     (not (is-falist (cons 'if rest)))
     :hints (("Goal" :in-theory (enable is-falist)))))

  (local
   (defthm lemma8
     (not (is-falist (cons 'not rest)))
     :hints (("Goal" :in-theory (enable is-falist)))))

  (local
   (defthm lemma9
     (implies (and (rp-syntaxp-lst subterms))
              (and (rp-syntaxp (car subterms))
                   (rp-syntaxp (cadr subterms))
                   (RP-SYNTAXP-LST (CDDR subterms))
                   (RP-SYNTAXP-LST (CDR subterms))
                   (rp-syntaxp (caddr subterms))))
     :rule-classes :forward-chaining))

  (local
   (defthm lemma10
     (implies (and (RP-SYNTAXP TERM)
                   (NOT (EQUAL (CAR TERM) 'QUOTE)))
              (RP-SYNTAXP-LST (CDR TERM)))
     :hints (("Goal"
              :cases ((is-rp term))
              :in-theory (e/d (is-rp) ())))))

  (encapsulate
    nil

    (local
     (defthm rp-syntaxp-cons-car-term-and-rp-rw-subterms-lemma
       (implies
        (and (equal (car term) 'rp)
             (rp-syntaxp term))
        (let ((res (mv-nth
                    0 (rp-rw (cadr term)
                             dont-rw
                             context limit
                             rules-alist exc-rules meta-rules iff-flg rp-state state))))
          (and
           (consp res)
           (equal (car res) 'quote)
           (consp (cdr res))
           (not (booleanp (cadr res)))
           (symbolp (cadr res))
           (not (cddr res))
           (not (equal (cadr res) 'quote))
           (not (equal (cadr res) 'rp)))))

       :hints (("Goal"
                :expand (;(RP-SYNTAXP TERM)
                         (rp-rw (cadr term)
                                dont-rw context limit rules-alist
                                exc-rules meta-rules iff-flg rp-state state))

                :in-theory (e/d (is-rp) ())))))

    (defthm rp-syntaxp-cons-car-term-and-rp-rw-subterms
      (implies
       (and
        (rp-syntaxp term)
        (rp-syntaxp-lst
         (mv-nth
          0 (rp-rw-subterms (cdr term) dont-rw context
                            limit rules-alist exc-rules meta-rules rp-state state))))
       (rp-syntaxp
        (cons (car term)
              (mv-nth  0 (rp-rw-subterms (cdr term) dont-rw context limit
                                         rules-alist exc-rules meta-rules rp-state state)))))
      :hints (("goal"
               :expand ((RP-RW-SUBTERMS (CDDR TERM)
                                        (MV-NTH 1
                                                (RP-RW (CADR TERM)
                                                       DONT-RW CONTEXT (+ -1 LIMIT)
                                                       RULES-ALIST EXC-RULES
                                                       META-RULES NIL RP-STATE STATE))
                                        CONTEXT (+ -1 LIMIT)
                                        RULES-ALIST EXC-RULES META-RULES
                                        (MV-NTH 2
                                                (RP-RW (CADR TERM)
                                                       DONT-RW CONTEXT (+ -1 LIMIT)
                                                       RULES-ALIST EXC-RULES
                                                       META-RULES NIL RP-STATE STATE))
                                        STATE)
                        (RP-RW-SUBTERMS (CDR TERM)
                                        DONT-RW CONTEXT LIMIT RULES-ALIST
                                        EXC-RULES META-RULES RP-STATE STATE))
               :in-theory (e/d (is-rp rp-rw-subterms) (rp-rw))))))

  (defthm pseudo-termp2-is-if-lemma
    (implies (and (is-if term)
                  (pseudo-termp2 term))
             (and (pseudo-termp2 (cadr term))
                  (pseudo-termp2 (caddr term))
                  (pseudo-termp2 (cadddr term))))
    :hints (("goal"
             :in-theory (e/d (is-if) ()))))

  (defthm all-falist-consistent-is-if-lemma
    (implies (and (IS-IF TERM)
                  (all-falist-consistent term))
             (and (all-falist-consistent (cadr term))
                  (all-falist-consistent (caddr term))
                  (all-falist-consistent (cadddr term))))
    :rule-classes :forward-chaining
    :hints (("Goal"
             :in-theory (e/d (is-if) ()))))

  (defthm rp-syntaxp-is-if
    (implies (and (IS-IF TERM)
                  (rp-syntaxp term))
             (and (rp-syntaxp (cadr term))
                  (rp-syntaxp (caddr term))
                  (rp-syntaxp (cadddr term))))
    :rule-classes :forward-chaining
    :hints (("Goal"
             :in-theory (e/d (is-if) ()))))

  (local
   (in-theory (disable (:REWRITE
                        NOT-INCLUDE-FALIST-ALL-FALIST-CONSISTENT)
                       (:REWRITE PSEUDO-TERMP2-IMPLIES-CDR-LISTP)
                       (:REWRITE ACL2::FN-CHECK-DEF-NOT-QUOTE)
                       (:REWRITE NOT-INCLUDE-RP)
                       #|(:REWRITE
                       HONS-GET-IS-RESOLVE-ASSOC-EQ-VALUE-REC)||#
                       (:REWRITE
                        ALL-FALIST-CONSISTENT-LST-RP-EXTRACT-CONTEXT)
                       (:REWRITE ALL-FALIST-CONSISTENT-LST-APPEND))))

  (with-output
    :off (warning event  prove  observation)
    :gag-mode :goals
    :on error
    (defthm-rp-rw
      (defthm pseudo-termp2-rp-rw
        (implies (and (PSEUDO-TERMP2 TERM)
                      (all-falist-consistent term)
                      (rp-meta-valid-syntax-listp meta-rules state)
                      (CONTEXT-SYNTAXP CONTEXT)
                      (rp-syntaxp term)
                      (SYMBOL-aLISTP EXC-RULES)
                      (RULES-ALISTP RULES-ALIST))
                 (let ((res (mv-nth 0
                                    (rp-rw term dont-rw context limit rules-alist
                                           exc-rules meta-rules iff-flg rp-state state))))
                   (and (pseudo-termp2 res)
                        (rp-syntaxp res)
                        (all-falist-consistent res))))
        :flag rp-rw)

      (defthm pseudo-termp2-rp-rw-rule
        (implies (and (PSEUDO-TERMP2 TERM)
                      (all-falist-consistent term)
                      (RULE-LIST-SYNTAXP RULES-FOR-TERM)
                      (rp-meta-valid-syntax-listp meta-rules state)
                      (CONTEXT-SYNTAXP CONTEXT)
                      (rp-syntaxp term)
                      (RULES-ALISTP RULES-ALIST)
                      (SYMBOL-aLISTP EXC-RULES))
                 (let ((res (mv-nth 1
                                    (rp-rw-rule TERM dont-rw RULES-FOR-TERM CONTEXT LIMIT RULES-ALIST
                                                EXC-RULES meta-rules IFF-FLG rp-state STATE))))
                   (and (pseudo-termp2 res)
                        (rp-syntaxp res)
                        (all-falist-consistent res))))
        :flag rp-rw-rule)

      (defthm pseudo-termp2-rp-rw-if
        (implies (and (pseudo-termp2 term)
                      (all-falist-consistent term)
                      (context-syntaxp context)
                      (rp-meta-valid-syntax-listp meta-rules state)
                      (rules-alistp rules-alist)
                      (rp-syntaxp term)
                      (symbol-alistp exc-rules))
                 (let ((res (mv-nth 0
                                    (rp-rw-if term dont-rw context limit rules-alist
                                              exc-rules meta-rules iff-flg rp-state state))))
                   (and (pseudo-termp2 res)
                        (rp-syntaxp res)
                        (all-falist-consistent res))))
        :flag rp-rw-if)

      (defthm pseudo-termp2-rp-rw-subterms
        (implies (and (PSEUDO-TERM-LISTP2 SUBTERMS)
                      (all-falist-consistent-lst subterms)
                      (context-syntaxp context)
                      (rp-meta-valid-syntax-listp meta-rules state)
                      (rp-syntaxp-lst subterms)
                      (rules-alistp rules-alist)
                      (symbol-alistp exc-rules))
                 (let ((res (mv-nth 0 (rp-rw-subterms SUBTERMS DONT-RW CONTEXT LIMIT
                                                      RULES-ALIST EXC-RULES meta-rules rp-state STATE))))
                   (and (pseudo-term-listp2 res)
                        (rp-syntaxp-lst res)
                        (all-falist-consistent-lst res))))
        :flag rp-rw-subterms)

      :hints (("Goal"
               ;; :in-theory (disable pseudo-term-listp2
               ;;                     pseudo-termp2
               ;;                     all-falist-consistent-lst
               ;;                     all-falist-consistent)
               :expand
               ((rp-rw-subterms nil dont-rw context limit
                                rules-alist exc-rules meta-rules rp-state state)
                (rp-rw-if term dont-rw context limit rules-alist
                          exc-rules meta-rules iff-flg rp-state state)
                (rp-rw-subterms subterms dont-rw context limit
                                rules-alist exc-rules meta-rules rp-state state)
                (rp-rw term dont-rw context limit
                       rules-alist exc-rules meta-rules nil rp-state state)
                (rp-rw-rule term dont-rw
                            rules-for-term context limit rules-alist
                            exc-rules meta-rules iff-flg rp-state state)
                (rp-rw-rule term dont-rw nil context limit rules-alist
                            exc-rules meta-rules iff-flg rp-state state)
                (rp-rw term 1 context limit rules-alist
                       exc-rules meta-rules iff-flg rp-state state)
                (rp-rw term dont-rw context limit rules-alist
                       exc-rules meta-rules iff-flg rp-state state)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|(defthm rp-evl-of-extract-context
  (implies (rp-evl term a)
           (eval-and-all (rp-extract-context term) a))
  :hints (("Goal" :in-theory (enable rp-extract-context
                                     eval-and-all))))||#

(defthm rp-evl-of-extract-context
  (iff (eval-and-all (rp-extract-context term) a)
       (rp-evl term a))
  :hints (("Goal"
           :in-theory (e/d (rp-extract-context
                            eval-and-all) ()))))

(local
 (defthm hide-x-is-x
   (equal (hide x) x)
   :hints (("Goal"
            :expand (hide x)))))

(defthm rp-evl-of-dumb-negate-lit2
  (implies (pseudo-termp2 x)
           (iff (rp-evl (dumb-negate-lit2 x) a)
                (not (rp-evl x a))))
  :hints (("Goal"
           :in-theory (e/d (dumb-negate-lit2 not) ()))))

(local
 (in-theory (disable ACL2::CDR-OF-APPEND-WHEN-CONSP
                     RP-EQUAL
                     VALID-RULES-ALISTP-IMPLIES-RULES-ALISTP
                     PSEUDO-TERM-LISTP2-APPEND
                     RP-EXTRACT-CONTEXT
                     RP-RW-RULE-AUX
                     CDR-TERM-IS-ALL-FALIST-CONSISTENT-LST
                     IS-RP-PSEUDO-TERMP
                     IS-IF-PSEUDO-TERMP2
                     IS-IF-PSEUDO-TERMP2)))

(local
 (defthm lemma2
   (implies (consp TERM)
            (consp (mv-nth 0 (RP-EX-COUNTERPART term EXC-RULES rp-state STATE))))
   :hints (("Goal"
            :in-theory (e/d (rp-ex-counterpart) ())))))

(local
 (defthm lemma3
   (implies (and (not (equal car-term 'falist))
                 (all-falist-consistent-lst subterms))
            (all-falist-consistent (cons car-term subterms)))
   :hints (("Goal"
            :in-theory (e/d (all-falist-consistent
                             all-falist-consistent-lst
                             is-falist)
                            (falist-consistent))))))

(local
 (defthm lemma4
   (implies (and (consp term)
                 (not (quotep term))
                 (equal (rp-evl-lst (cdr term) a)
                        (rp-evl-lst subterms2 a)))
            (equal (rp-evl (cons (car term) subterms2) a)
                   (rp-evl term a)))
   :hints (("Goal"
            :in-theory (e/d (rp-evl-of-fncall-args) ())))))

(local
 (defthm lemma5
   (implies (is-falist term)
            (not (pseudo-termp2 (cadddr term))))
   :hints (("Goal"
            :in-theory (e/d (is-falist) ())))))

(local
 (defthm lemma6
   (implies (nonnil-p term)
            (rp-evl term a))
   :hints (("Goal"
            :in-theory (e/d (nonnil-p) ())))))

(local
 (defthm lemma7
   (implies (and (ALL-FALIST-CONSISTENT TERM)
                 (EQUAL (CAR TERM) 'IF)
                 (CONSP (CDR TERM))
                 (CONSP (CDDR TERM))
                 (CONSP (CDDDR TERM))
                 (NOT (CDDDDR TERM)))
            (ALL-FALIST-CONSISTENT (CADDDR TERM)))
   :hints (("Goal"
            :expand ((ALL-FALIST-CONSISTENT TERM)
                     (ALL-FALIST-CONSISTENT-LST (CDR TERM))
                     (ALL-FALIST-CONSISTENT-LST (CdDR TERM))
                     (ALL-FALIST-CONSISTENT-LST (CddDR TERM)))

            :in-theory (e/d (is-falist)
                            (all-falist-consistent
                             all-falist-consistent-lst))))))

(local
 (in-theory (enable
             pseudo-term-listp2-append
             rule-syntaxp-implies)))

(defthm valid-sc-dumb-negate-lit2
  (implies (valid-sc term a)
           (valid-sc (dumb-negate-lit2 term) a))
  :hints (("Goal"
           :expand ((VALID-SC (LIST 'NOT TERM) A))
           :in-theory (e/d (valid-sc
                            is-rp
                            is-if
                            dumb-negate-lit2) ()))))

(encapsulate
  nil

  (local

   (defthm lemma1
     (IMPLIES (AND (CONSP CONTEXT)
                   (CONSP (CAR CONTEXT))
                   (EQUAL (CAR (CAR CONTEXT)) 'EQUAL)
                   (CONSP (CDR (CAR CONTEXT)))
                   (CONSP (CDDR (CAR CONTEXT)))
                   (NOT (CDDDR (CAR CONTEXT)))
                   (VALID-SC (CADR (CAR CONTEXT)) A)
                   (VALID-SC-SUBTERMS CONTEXT A))
              (VALID-SC (CADDR (CAR CONTEXT)) A))
     :hints (("Goal"
              :expand ((VALID-SC-SUBTERMS CONTEXT A)
                       (VALID-SC (CAR CONTEXT) A))
              :in-theory (e/d (is-if is-rp) ())))))

  (local
   (defthm l-lemma2
     (IMPLIES (AND (CONSP CONTEXT)
                   (CONSP (CAR CONTEXT))
                   (EQUAL (CAR (CAR CONTEXT)) 'EQUAL)
                   (CONSP (CDR (CAR CONTEXT)))
                   (CONSP (CDDR (CAR CONTEXT)))
                   (NOT (CDDDR (CAR CONTEXT)))
                   (RP-EQUAL TERM (CADR (CAR CONTEXT)))
                   (VALID-SC TERM A)
                   (VALID-SC-SUBTERMS CONTEXT A))
              (VALID-SC (CADDR (CAR CONTEXT)) A))
     :hints (("Goal"
              :expand ((VALID-SC-SUBTERMS CONTEXT A)
                       (VALID-SC (CAR CONTEXT) A))
              :in-theory (e/d (is-if is-rp) ())))))

  (defthm valid-sc-rp-check-context
    (implies (and (valid-sc term a)
                  (valid-sc-subterms context a))
             (valid-sc (mv-nth 0 (rp-check-context term dont-rw context iff-flg)) a))
    :hints (("Goal"
             :expand ()
             :in-theory (e/d (rp-check-context) ()))))

  (defthm valid-sc-dumb-negate-lit2
    (implies (valid-sc term a)
             (valid-sc (dumb-negate-lit2 term) a))
    :hints (("Goal"
             :expand ((VALID-SC (LIST 'NOT TERM) A))
             :in-theory (e/d (valid-sc
                              is-rp
                              is-if
                              dumb-negate-lit2) ())))))

(local
 (defthm lemma0
   (implies (and (eval-and-all (context-from-rp term nil)
                               a)
                 (is-rp term))
            (eval-and-all (context-from-rp (caddr term) nil)
                          a))
   :hints (("goal"
            :in-theory (e/d (is-rp
                             context-from-rp)
                            (ex-from-rp-lemma1))))))

(local
 (defthm lemma1
   (implies (and (valid-sc term a)
                 (consp term)
                 (not (eq (car term) 'quote))
                 (not (is-if term)))
            (valid-sc-subterms (cdr term) a))
   :hints (("goal"
            :expand ((valid-sc term a)
                     (ex-from-rp term))
            :in-theory (e/d (is-rp) ())))))

(local
 (defthm lemma101
   (implies (and (rp-syntaxp-lst subterms))
            (and (rp-syntaxp (car subterms))
                 (rp-syntaxp (cadr subterms))
                 (RP-SYNTAXP-LST (CDDR subterms))
                 (RP-SYNTAXP-LST (CDR subterms))
                 (rp-syntaxp (caddr subterms))))
   :rule-classes :forward-chaining
   :hints (("Goal"
            :in-theory (e/d (rp-syntaxp
                             rp-syntaxp-lst) ())))))

(local
 (defthm lemma102
   (implies (and (pseudo-termp2 term)
                 (not (equal (car term) 'quote)))
            (pseudo-term-listp2 (cdr term)))
   :hints (("Goal"
            :in-theory (e/d (pseudo-term-listp2
                             pseudo-termp2) ())))))

(local
 (defthm lemma103
   (implies (and (RP-SYNTAXP TERM)
                 (NOT (EQUAL (CAR TERM) 'QUOTE)))
            (RP-SYNTAXP-LST (CDR TERM)))
   :hints (("Goal"
            :cases ((is-rp term))
            :in-theory (e/d (is-rp
                             rp-syntaxp-lst
                             rp-syntaxp) ())))))

#|(local
 (defthm lemma104
   (implies (and (is-falist (cons x y))
                 (all-falist-consistent (cons x y)))
            (and (all-falist-consistent (cadr y))
                 (falist-consistent (cons x y))))
   :hints (("Goal"
            :in-theory (e/d (all-falist-consistent is-falist) ())))))||#

(encapsulate
  nil
  (local
   (defthm i-lemma1
     (implies (and (equal (car term) 'rp)
                   (rp-syntaxp term))
              (case-match term
                (('rp ('quote type) &)
                 (and (symbolp type)
                      (not (booleanp type))
                      (not (equal type 'quote))
                      (not (equal type 'rp))))
                (& nil)))
     :hints (("goal"
              :in-theory (e/d (is-rp) ())))
     :rule-classes :forward-chaining))

  (local
   (defthm i-lemma2
     (implies
      (and (equal (car term) 'rp)
           (rp-syntaxp term))
      (equal (mv-nth 0 (rp-rw (cadr term)
                              dont-rw
                              context limit
                              rules-alist exc-rules meta-rules iff-flg rp-state state))
             (cadr term)))
     :hints (("goal"
              :expand (rp-rw (cadr term)
                             dont-rw
                             context limit
                             rules-alist exc-rules meta-rules iff-flg rp-state state)
              :in-theory (e/d () ())))))

  (defthm eval-and-all-context-from-when-valid-sc
    (implies (valid-sc term a)
             (eval-and-all (context-from-rp term nil) a))
    :hints (("goal"
             :cases ((is-rp term))
;:induct (context-from-rp term nil)
             :in-theory (e/d (context-from-rp
                              is-rp
                              is-if
                              valid-sc)
                             (ex-from-rp-lemma1
                              valid-sc-subterms)))))

  (local
   (defthm i-lemma3
     (implies (and (equal (rp-evl rp-rw-caddr-term a)
                          (rp-evl caddr-term a))
                   (valid-sc rp-rw-caddr-term a)
                   (valid-sc term a)
                   (equal term (list 'rp cadr-term caddr-term)))
              (valid-sc (list 'rp cadr-term rp-rw-caddr-term) a))
     :otf-flg t
     :hints (("goal"
              :use ((:instance evl-of-extract-from-rp
                               (term rp-rw-caddr-term))
                    (:instance evl-of-extract-from-rp
                               (term caddr-term)))
              :expand ((valid-sc (list 'rp cadr-term rp-rw-caddr-term) a)
                       (ex-from-rp (list 'rp cadr-term rp-rw-caddr-term))
                       (ex-from-rp (list 'rp cadr-term caddr-term))
                       (context-from-rp (list 'rp cadr-term rp-rw-caddr-term)
                                        nil)
                       (context-from-rp (list 'rp cadr-term caddr-term)
                                        nil)
                       (valid-sc (list 'rp cadr-term caddr-term) a))
              :in-theory (e/d (is-if
                               rp-evl-of-fncall-args
                               eval-and-all
                               valid-sc
                               is-rp)
                              (evl-of-extract-from-rp
                               valid-sc-ex-from-rp-2))))))

  (defthm valid-sc-cons-car-term-and-rp-rw-subterms
    (implies
     (and
      (valid-sc term a)
      (consp term)
      (rp-syntaxp term)
      (equal (rp-evl-lst
              (mv-nth 0 (rp-rw-subterms (cdr term) dont-rw context limit
                                        rules-alist exc-rules meta-rules rp-state state))
              a)
             (rp-evl-lst (cdr term) a))
      (valid-sc-subterms
       (mv-nth 0 (rp-rw-subterms (cdr term) dont-rw context limit
                                 rules-alist exc-rules meta-rules rp-state state))
       a))
     (valid-sc
      (cons (car term)
            (mv-nth  0 (rp-rw-subterms (cdr term) dont-rw context limit
                                       rules-alist exc-rules meta-rules  rp-state state)))
      a))
    :otf-flg t
    :hints (("goal"
             :do-not-induct t
             :expand ((valid-sc term a)
                      (RP-RW-SUBTERMS (CDR TERM)
                                      DONT-RW CONTEXT LIMIT RULES-ALIST
                                      EXC-RULES META-RULES RP-STATE STATE)
                      (RP-RW-SUBTERMS (CDDR TERM)
                                      (MV-NTH 1
                                              (RP-RW (CADR TERM)
                                                     DONT-RW CONTEXT (+ -1 LIMIT)
                                                     RULES-ALIST EXC-RULES
                                                     META-RULES NIL RP-STATE STATE))
                                      CONTEXT (+ -1 LIMIT)
                                      RULES-ALIST EXC-RULES META-RULES
                                      (MV-NTH 2
                                              (RP-RW (CADR TERM)
                                                     DONT-RW CONTEXT (+ -1 LIMIT)
                                                     RULES-ALIST EXC-RULES
                                                     META-RULES NIL RP-STATE STATE))
                                      STATE))
             :in-theory (e/d (is-rp is-if valid-sc
                                    context-from-rp
                                    rp-rw
                                    rp-rw-subterms)
                             (rp-rw
                              (:REWRITE ACL2::O-P-O-INFP-CAR)
                              (:REWRITE VALID-SC-CADR)
                              (:TYPE-PRESCRIPTION INCLUDE-FNC)
                              (:REWRITE EVAL-AND-ALL-CONTEXT-FROM-RP)
                              (:DEFINITION PSEUDO-TERMP2)
                              (:REWRITE PSEUDO-TERMP2-RP-RW)
                              ex-from-rp-lemma1))))))

(local
 (defthm lemma105
   (implies (and (rp-syntaxp term)
                 (not (equal (car term) 'quote)))
            (and (rp-syntaxp (cadr term))))
   :rule-classes :forward-chaining
   :hints (("goal"
            :expand (rp-syntaxp term)
            :in-theory (e/d (rp-syntaxp
                             is-rp) ())))))

(local
 (defthm lemma106
   (is-if (list 'if x y z))
   :hints (("goal"
            :in-theory (e/d (is-if) ())))))

#|(defthm valid-sc-cons-car-term-and-rp-rw-subterms
  (implies
   (and
        (valid-sc-subterms subterms a))
   (valid-sc (cons (car term) subterms) a))
  :hints (("goal"
           :expand ((valid-sc (cons (car term) subterms) a)
                    (valid-sc (cons 'rp subterms) a))
           :in-theory (e/d (is-rp is-if) (rp-rw)))))||#

(local
 (in-theory (e/d (context-syntaxp-implies)
                 (rp-syntaxp-lst
                  rp-syntaxp))))

(local
 (defthm lemma107
   (implies (and (all-falist-consistent term)
                 (equal (car term) 'if)
                 (consp (cdr term)))
            (all-falist-consistent (cadr term)))
   :rule-classes :forward-chaining
   :hints (("goal"
            :in-theory (e/d (all-falist-consistent
                             is-falist) ())))))

(local
 (defthm lemma108
   (implies (and
             (valid-sc term a)
             (not (rp-evl (cadr term) a))
             (is-if term))
            (valid-sc (cadddr term) a))
   :hints (("goal"
            :in-theory (e/d (valid-sc
                             is-if) ())))))

(local
 (defthm lemma109
   (implies (and
             (valid-sc term a)
             (rp-evl (cadr term) a)
             (is-if term))
            (valid-sc (caddr term) a))
   :hints (("goal"
            :in-theory (e/d (valid-sc
                             is-if) ())))))

(defthm is-if-implies
  (implies (is-if term)
           (case-match term (('if & & &) t)
             (& nil)))
  :rule-classes :forward-chaining
  :hints (("goal"
           :in-theory (e/d (is-if) ()))))

(local
 (in-theory (disable rp-apply-bindings-to-evl
                     rp-apply-bindings-subterms-to-evl-lst)))

(local
 (in-theory
  (disable
   (:rewrite
    not-include-falist-all-falist-consistent)
   (:rewrite pseudo-termp2-implies-cdr-listp)
   (:rewrite not-include-rp-means-rp-syntaxp-lst)
   (:type-prescription include-fnc-subterms)
   (:type-prescription include-fnc)
   (:rewrite rp-evl-of-rp-equal)
   (:REWRITE ALL-FALIST-CONSISTENT-CADDDR)

   (:REWRITE ALL-FALIST-CONSISTENT-CADDR)
   (:REWRITE ACL2::O-P-O-INFP-CAR)
   (:REWRITE PSEUDO-TERMP2-CADDR)
   (:REWRITE PSEUDO-TERMP2-CADR)
   (:REWRITE PSEUDO-TERMP2-IMPLIES-SUBTERMS)
   (:rewrite
    not-include-falist-all-falist-consistent-lst))))

(local
 (in-theory
  (e/d (context-syntaxp
        is-if-implies
        valid-rules-alistp-implies-rules-alistp)
       (iff))))

(local
 (defthm is-if-rp-ex-counterpart
   (implies (not (is-if term))
            (not (is-if (mv-nth 0 (rp-ex-counterpart term
                                                     exc-rules
                                                     rp-state
                                                     state)))))
   :hints (("Goal"
            :in-theory (e/d (is-if
                             rp-ex-counterpart) ())))))

(with-output
  :off (warning event  prove  observation)
  :gag-mode :goals
  :on error
  (defthm-rp-rw
    (defthm rp-evl-and-side-cond-consistent-of-rp-rw
      (implies (and (pseudo-termp2 term)
                    (alistp a)
                    (all-falist-consistent term)
                    (rp-evl-meta-extract-global-facts :state state)
                    (eval-and-all context a)
                    (rp-syntaxp term)
                    (valid-sc term a)
                    (context-syntaxp context)
                    (valid-sc-subterms context a)
                    (valid-rp-meta-rule-listp meta-rules state)
                    (rp-meta-valid-syntax-listp meta-rules state)
                    (symbol-alistp exc-rules)
                    (valid-rules-alistp rules-alist))
               (let ((res
                      (mv-nth 0
                              (rp-rw term dont-rw context limit rules-alist
                                     exc-rules meta-rules iff-flg rp-state state))))
                 (and (valid-sc res a)
                      (if iff-flg
                          (iff (rp-evl res a) (rp-evl term a))
                        (equal (rp-evl res a) (rp-evl term a))))))
      :flag rp-rw)

    (defthm rp-evl-and-side-cond-consistent-rp-rw-rule
      (implies (and (pseudo-termp2 term)
                    (alistp a)
                    (all-falist-consistent term)
                    (rp-evl-meta-extract-global-facts :state state)
                    (valid-rulesp rules-for-term)
                    (context-syntaxp context)
                    (rp-syntaxp term)
                    (valid-sc-subterms context a)
                    (valid-rp-meta-rule-listp meta-rules state)
                    (rp-meta-valid-syntax-listp meta-rules state)
                    (eval-and-all context a)
                    (valid-sc term a)
                    (valid-rules-alistp rules-alist)
                    (symbol-alistp exc-rules))
               (let ((res
                      (mv-nth 1
                              (rp-rw-rule term dont-rw rules-for-term context limit rules-alist
                                          exc-rules meta-rules iff-flg rp-state state))))
                 (and (valid-sc res a)
                      (if iff-flg
                          (iff (rp-evl res a) (rp-evl term a))
                        (equal (rp-evl res a) (rp-evl term a))))))
      :flag rp-rw-rule)

    (defthm rp-evl-and-side-cond-consistent-rp-rw-if
      (implies (and (pseudo-termp2 term)
                    (alistp a)
                    (all-falist-consistent term)
                    (rp-evl-meta-extract-global-facts :state state)
                    (context-syntaxp context)
                    (rp-syntaxp term)
                    (valid-sc-subterms context a)
                    (valid-rp-meta-rule-listp meta-rules state)
                    (rp-meta-valid-syntax-listp meta-rules state)
                    (eval-and-all context a)
                    (valid-sc term a)
                    (valid-rules-alistp rules-alist)
                    (symbol-alistp exc-rules))
               (let ((res
                      (mv-nth 0
                              (rp-rw-if term dont-rw context limit rules-alist
                                        exc-rules meta-rules iff-flg rp-state state))))
                 (and  (valid-sc res a)
                       (if iff-flg
                           (iff (rp-evl res a) (rp-evl term a))
                         (equal (rp-evl res a) (rp-evl term a))))))
      :flag rp-rw-if)

    (defthm rp-evl-and-side-cond-consistent-rp-rw-subterms
      (implies (and (pseudo-term-listp2 subterms)
                    (alistp a)
                    (all-falist-consistent-lst subterms)
                    (rp-evl-meta-extract-global-facts :state state)
                    (context-syntaxp context)
                    (valid-sc-subterms context a)
                    (rp-syntaxp-lst subterms)
                    (eval-and-all context a)
                    (valid-rules-alistp rules-alist)
                    (valid-rp-meta-rule-listp meta-rules state)
                    (rp-meta-valid-syntax-listp meta-rules state)
                    (valid-sc-subterms subterms a)
                    (symbol-alistp exc-rules))
               (let ((res
                      (mv-nth 0 (rp-rw-subterms subterms dont-rw context limit
                                                rules-alist exc-rules
                                                meta-rules rp-state state))))
                 (and (valid-sc-subterms res a)
                      (equal (rp-evl-lst res a) (rp-evl-lst subterms a)))))
      :flag rp-rw-subterms)

    :hints (("goal"
             :expand
             ((:free (x y z)
                     (valid-sc (list 'if x y z) a))
              (rp-rw-rule term dont-rw rules-for-term context limit
                          rules-alist exc-rules meta-rules nil rp-state state)
              (rp-rw-rule term dont-rw
                          rules-for-term context limit rules-alist
                          exc-rules meta-rules iff-flg rp-state state)
              (rp-rw-if term dont-rw context limit rules-alist
                        exc-rules meta-rules iff-flg rp-state state)
              (rp-rw term dont-rw context limit rules-alist
                     exc-rules meta-rules iff-flg rp-state state)
              (rp-rw term dont-rw context limit
                     rules-alist exc-rules meta-rules nil rp-state state)

              (rp-rw-if term dont-rw context limit
                        rules-alist exc-rules meta-rules nil rp-state state)
              (rp-rw-subterms subterms dont-rw context
                              limit rules-alist exc-rules meta-rules rp-state state)

              (rp-rw-subterms nil dont-rw context
                              limit rules-alist exc-rules meta-rules rp-state state))))))



(local
 (in-theory (disable natp)))

(local 
 (encapsulate
   nil
   (local
    (include-book "ihs/ihs-lemmas" :dir :system))


   (defthm natp-logcdr
     (implies (and (natp x))
              (natp (acl2::logcdr x)))
     :rule-classes :type-prescription)

   (defthm natp-logcar
     (implies (and (natp x))
              (natp (acl2::logcar x)))
     :rule-classes :type-prescription)

   (defthm natp-logapp
     (implies (and (natp y)
                   (natp x)
                   (natp size))
              (natp (logapp size x y)))
     :rule-classes :type-prescription)

   (defthm natp-logapp-rw
     (implies (and (natp y)
                   (natp x)
                   (natp size))
              (natp (logapp size x y))))))




(local
 (defthm rules-alistp-lemma1
   (implies (rules-alistp rules-alist)
            (RULE-LIST-SYNTAXP
             (cdr (hons-get key rules-alist))))
   :hints (("Goal"
            :do-not-induct t
            :induct (hons-assoc-equal key rules-alist)
            :in-theory (e/d (rules-alistp
                             ALISTP
                             SYMBOL-LISTP
                             STRIP-CARS
                             STRIP-CDRS
                             hons-get
                             hons-assoc-equal
                             RULE-LIST-LIST-SYNTAXP
                             ) ())))))
            

(with-output
  :off (warning event  prove  observation)
  :gag-mode :goals
  :on error
  (defthm-rp-rw
    (defthm natp-of-rp-rw-dont-rw
      (implies (and
                ;(rp-evl-meta-extract-global-facts :state state)
                ;(valid-rp-meta-rule-listp META-RULES STATE)
                ;(rp-meta-valid-syntax-listp meta-rules state)
                (natp dont-rw)
                (rules-alistp rules-alist))
               (let ((res
                      (mv-nth 1
                              (rp-rw term dont-rw context limit rules-alist
                                     exc-rules meta-rules iff-flg rp-state state))))
                 (natp res)))
      :rule-classes :type-prescription
      :flag rp-rw)

    (defthm natp-of-rp-rw-rule-dont-rw
      (implies (and ;(rp-evl-meta-extract-global-facts :state state)
                    (RULE-LIST-SYNTAXP rules-for-term)
                    ;(valid-rp-meta-rule-listp meta-rules state)
                    ;(rp-meta-valid-syntax-listp meta-rules state)
                    (rules-alistp rules-alist)
                    (natp dont-rw))
               (let ((res
                      (mv-nth 2
                              (rp-rw-rule term dont-rw rules-for-term context limit rules-alist
                                          exc-rules meta-rules iff-flg rp-state state))))
                 (natp res)))
      :rule-classes :type-prescription
      :flag rp-rw-rule)

    (defthm natp-of-rp-rw-if-dont-rw
      (implies (and ;(rp-evl-meta-extract-global-facts :state state)
                    ;(valid-rp-meta-rule-listp meta-rules state)
                    ;(rp-meta-valid-syntax-listp meta-rules state)
                    (natp dont-rw)
;;(valid-rules-alistp rules-alist)
                    (rules-alistp rules-alist)
                    )
               (let ((res
                      (mv-nth 1
                              (rp-rw-if term dont-rw context limit rules-alist
                                        exc-rules meta-rules iff-flg rp-state state))))
                 (natp res)))
      :rule-classes :type-prescription
      :flag rp-rw-if)

    (defthm natp-of-rp-rw-subterms-dont-rw
      (implies (and ;(rp-evl-meta-extract-global-facts :state state)
                    ;(valid-rules-alistp rules-alist)
                    ;(valid-rp-meta-rule-listp meta-rules state)
                    ;(rp-meta-valid-syntax-listp meta-rules state)
                    (rules-alistp rules-alist)
                    (natp dont-rw))
               (let ((res
                      (mv-nth 1 (rp-rw-subterms subterms dont-rw context limit
                                                rules-alist exc-rules
                                                meta-rules rp-state state))))
                 (natp res)))
      :rule-classes :type-prescription
      :flag rp-rw-subterms)

    :hints (("goal"
             :expand
             ((:free (x y z)
                     (valid-sc (list 'if x y z) a))
              (rp-rw-rule term dont-rw rules-for-term context limit
                          rules-alist exc-rules meta-rules nil rp-state state)
              (rp-rw-rule term dont-rw
                          rules-for-term context limit rules-alist
                          exc-rules meta-rules iff-flg rp-state state)
              (rp-rw-if term dont-rw context limit rules-alist
                        exc-rules meta-rules iff-flg rp-state state)
              (rp-rw term dont-rw context limit rules-alist
                     exc-rules meta-rules iff-flg rp-state state)
              (rp-rw term dont-rw context limit
                     rules-alist exc-rules meta-rules nil rp-state state)

              (rp-rw-if term dont-rw context limit
                        rules-alist exc-rules meta-rules nil rp-state state)
              (rp-rw-subterms subterms dont-rw context
                              limit rules-alist exc-rules meta-rules rp-state state)

              (rp-rw-subterms nil dont-rw context
                              limit rules-alist exc-rules meta-rules rp-state state))))))
