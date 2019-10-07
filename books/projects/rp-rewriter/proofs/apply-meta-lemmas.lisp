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


; Lemmas regarding the meta rules that could be added to the rewriter.

(in-package "RP")

(include-book "../rp-rewriter")
(include-book "aux-function-lemmas")
(include-book "rp-state-functions-lemmas")
(include-book "proof-functions")


(local
 (in-theory (enable RP-RW-META-RULES
                    RP-RW-META-RULE)))

(defthm rp-rw-meta-rule-returns-valid-termp
  (implies (and (rp-valid-termp term)
                (rp-meta-valid-syntaxp-sk meta-rule state))
           (rp-valid-termp (mv-nth 1 (rp-rw-meta-rule term meta-rule rp-state state))))
  :hints (("goal"
           :use ((:instance rp-meta-valid-syntaxp-sk-necc (state- state)))
           :in-theory (e/d (rp-meta-valid-syntax-listp
                            mv-nth
                            rp-meta-valid-syntaxp)
                           (all-falist-consistent
                            rp-meta-valid-syntaxp-sk
                            rp-meta-dont-rw
                            rp-meta-trig-fnc
                            rp-meta-syntax-verified
                            rp-meta-fnc
                            rp-syntaxp
                            pseudo-termp2)))))

(defthm rp-rw-meta-rules-returns-valid-termp
  (implies (and (rp-valid-termp term)
                (rp-meta-valid-syntax-listp meta-rules state))
           (rp-valid-termp (mv-nth 1 (rp-rw-meta-rules term meta-rules rp-state state))))
  :hints (("goal"
           :in-theory (e/d (rp-meta-valid-syntax-listp
                            mv-nth
                            rp-meta-valid-syntaxp)
                           (all-falist-consistent
                            rp-rw-meta-rule
                            rp-meta-valid-syntaxp-sk-necc
                            rp-meta-dont-rw
                            rp-meta-trig-fnc
                            ;;magic-ev-fncall
                            rp-meta-fnc
                            rp-syntaxp
                            pseudo-termp2)))))


#|(local
 (defthm meta-fnc-is-logicp
   (implies (RP-META-VALID-SYNTAXP-SK META-RULE STATE)
            (ACL2::LOGICP (RP-META-FNC META-RULE)
                          (W STATE)))
   :hints (("Goal"
            :in-theory (e/d (RP-META-VALID-SYNTAXP) ())))))||#

(defthm rp-rw-meta-rule-returns-valid-dont-rw
  (implies (and (rp-meta-valid-syntaxp-sk meta-rule state))
           (natp (mv-nth 2 (rp-rw-meta-rule term meta-rule rp-state
                                                 state))))
  :otf-flg t
  :rule-classes :type-prescription
  :hints (("goal"
           :use ((:instance rp-meta-valid-syntaxp-sk-necc (state- state)))
           :expand ((:free (x y) (mv-nth x y)))
           :in-theory (e/d (rp-meta-valid-syntax-listp
                            rp-meta-valid-syntaxp)
                           (all-falist-consistent
                            rp-meta-valid-syntaxp-sk-necc
                            rp-meta-valid-syntaxp-sk
                            RP-META-SYNTAX-VERIFIED
                            rp-meta-dont-rw
                            rp-meta-trig-fnc
                            rp-meta-fnc
                            rp-syntaxp
                            mv-nth
                            w
                            (:DEFINITION ACL2::APPLY$-BADGEP)
                            (:DEFINITION SUBSETP-EQUAL)
                            (:DEFINITION MEMBER-EQUAL)
                            (:REWRITE DEFAULT-CDR)
                            (:REWRITE
                             ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1)
                            (:REWRITE ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                            (:REWRITE ACL2::APPLY$-BADGEP-PROPERTIES . 2)
                            (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                            (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 2)
                            (:REWRITE DEFAULT-CAR)
                            (:REWRITE PSEUDO-TERM-LISTP2-IS-TRUE-LISTP)
                            (:DEFINITION PSEUDO-TERM-LISTP2)
                            pseudo-termp2)))))

(defthm rp-rw-meta-rule-returns-valid-dont-rw-size
  (implies (and (rp-meta-valid-syntaxp-sk meta-rule state))
           (natp (mv-nth 3 (rp-rw-meta-rule term meta-rule rp-state
                                                 state))))
  :otf-flg t
  :rule-classes :type-prescription
  :hints (("goal"
           :use ((:instance rp-meta-valid-syntaxp-sk-necc (state- state)))
           :expand ((:free (x y) (mv-nth x y)))
           :in-theory (e/d (rp-meta-valid-syntax-listp
                            mv-nth
                            rp-meta-valid-syntaxp)
                           (all-falist-consistent
                            rp-meta-valid-syntaxp-sk-necc
                            rp-meta-valid-syntaxp-sk
                            (:DEFINITION ACL2::APPLY$-BADGEP)
                            (:DEFINITION SUBSETP-EQUAL)
                            (:DEFINITION MEMBER-EQUAL)
                            (:REWRITE DEFAULT-CDR)
                            (:REWRITE
                             ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1)
                            (:REWRITE ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                            (:REWRITE ACL2::APPLY$-BADGEP-PROPERTIES . 2)
                            (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                            (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 2)
                            (:REWRITE DEFAULT-CAR)
                            (:REWRITE PSEUDO-TERM-LISTP2-IS-TRUE-LISTP)
                            (:TYPE-PRESCRIPTION
                                    RP-STATE-PUSH-META-TO-RW-STACK)
                            RP-META-SYNTAX-VERIFIED
                            rp-meta-dont-rw
                            rp-meta-trig-fnc
                            rp-meta-fnc
                            rp-syntaxp
                            pseudo-termp2)))))

(defthm rp-rw-meta-rules-returns-valid-dont-rw
  (implies (and (rp-meta-valid-syntax-listp meta-rules state))
           (natp (mv-nth 2 (rp-rw-meta-rules term meta-rules rp-state
                                             state))))
  :RULE-CLASSES :type-prescription
  :hints (("goal"
           :expand (RP-RW-META-RULES TERM NIL RP-STATE STATE)
           :in-theory (e/d (rp-meta-valid-syntax-listp
                            RP-RW-META-RULES
                            mv-nth
                            )
                           (all-falist-consistent
                            natp
                            acl2::MV-NTH-CONS-META
                            RP-META-SYNTAX-VERIFIED
                            RP-META-VALID-SYNTAXP-SK
                            RP-RW-META-RULE
                            rp-meta-valid-syntaxp
                            rp-meta-dont-rw
                            rp-meta-trig-fnc
                            rp-meta-fnc
                            rp-syntaxp
                            pseudo-termp2)))))

(defthm rp-rw-meta-rules-returns-valid-dont-rw-size
  (implies (and (rp-meta-valid-syntax-listp meta-rules state))
           (natp (mv-nth 3 (rp-rw-meta-rules term meta-rules rp-state
                                                  state))))
  :RULE-CLASSES :type-prescription
  :hints (("goal"
           :in-theory (e/d (rp-meta-valid-syntax-listp
                            RP-RW-META-RULES
                            mv-nth
                            )
                           (all-falist-consistent
                            acl2::MV-NTH-CONS-META
                            RP-META-SYNTAX-VERIFIED
                            RP-META-VALID-SYNTAXP-SK
                            RP-RW-META-RULE
                            rp-meta-valid-syntaxp
                            rp-meta-dont-rw
                            rp-meta-trig-fnc
                            rp-meta-fnc
                            rp-syntaxp
                            pseudo-termp2)))))

(defthm rp-rw-meta-rule-returns-valid-sc
  (implies (and (valid-sc term a)
                (rp-valid-termp term)
                (valid-rp-meta-rulep meta-rule state))
           (valid-sc (mv-nth 1 (rp-rw-meta-rule term meta-rule rp-state state)) a))
  :hints (("Goal"
           :do-not '(preprocess)
           :use ((:instance valid-rp-meta-rulep-necc
                            (rule meta-rule)
                            (state- state))
                 (:instance evals-equal-sk-necc
                            (term1 term)
                            (a a)
                            (term2 (mv-nth 1 (rp-rw-meta-rule term meta-rule rp-state state)))))
           :in-theory (e/d (mv-nth)
                           (valid-rp-meta-rulep-necc

                            rp-syntaxp
                            all-falist-consistent
                            pseudo-termp2
                            
                            RP-META-SYNTAX-VERIFIED
                            acl2::MV-NTH-CONS-META
                            VALID-SC
                            rp-meta-dont-rw
                            rp-meta-trig-fnc
                            (:DEFINITION ACL2::APPLY$-BADGEP)
                            (:REWRITE ACL2::APPLY$-BADGEP-PROPERTIES . 3)
                            (:DEFINITION SUBSETP-EQUAL)
                            (:DEFINITION MEMBER-EQUAL)
                            (:REWRITE DEFAULT-CAR)
                            (:REWRITE
                                    ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1)
                            (:REWRITE DEFAULT-CDR)
                            rp-meta-fnc
                            VALID-RP-META-RULEP

                            (:REWRITE PSEUDO-TERM-LISTP2-IS-TRUE-LISTP))))))

(defthm rp-rw-meta-rules-returns-valid-sc
  (implies (and (valid-sc term a)
                (rp-valid-termp term)
                (valid-rp-meta-rule-listp meta-rules state))
           (valid-sc (mv-nth 1 (rp-rw-meta-rules term meta-rules rp-state state)) a))
  :hints (("Goal"
           :do-not '(preprocess)
           :use ((:instance valid-rp-meta-rulep-necc
                            (rule (car meta-rules))
                            (state- state)))
           :in-theory (e/d (mv-nth
                            RP-RW-META-RULES)
                           (valid-rp-meta-rulep-necc
                            rp-rw-meta-rule
                            rp-meta-dont-rw
                            valid-sc
                            rp-meta-trig-fnc
                            rp-meta-fnc
                            VALID-RP-META-RULEP)))))

(defthm rp-rw-meta-rule-evals-correctly
  (implies (and (valid-rp-meta-rulep meta-rule state)
                (rp-valid-termp term)
                (valid-sc term a))
           (equal (rp-evl (mv-nth 1 (rp-rw-meta-rule term meta-rule rp-state state))
                          a)
                  (rp-evl term a)))

  :hints (("Goal"
           :expand ((:free (x y) (mv-nth x y)))
           :use ((:instance valid-rp-meta-rulep-necc
                            (rule meta-rule)
                            (term term)
                            (state- state))
                 (:instance evals-equal-sk-necc
                            (term1 term)
                            (a a)
                            (term2 (cadr
                                    (MAGIC-EV-FNCALL (RP-META-FNC META-RULE)
                                                     (LIST TERM)
                                                     STATE T NIL))))
                 (:instance evals-equal-sk-necc
                            (term1 term)
                            (a a)
                            (term2 (car (cadr
                                         (MAGIC-EV-FNCALL (RP-META-FNC META-RULE)
                                                          (LIST TERM)
                                                          STATE T NIL))))))
           :in-theory (e/d ()
                           (evals-equal-sk
                            evals-equal-sk-necc
                            valid-rp-meta-rulep-necc
                            RP-META-DONT-RW
                            RP-META-FNC
                            acl2::MV-NTH-CONS-META
                            EX-FROM-RP
                            VALID-SC
                            ALL-FALIST-CONSISTENT
                            pseudo-termp2
                            RP-META-SYNTAX-VERIFIED
                            VALID-RP-META-RULEP)))))

(defthm rp-rw-meta-rules-evals-correctly
  (implies (and (valid-rp-meta-rule-listp meta-rules state)
                (rp-valid-termp term)
                (valid-sc term a))
           (equal (rp-evl (mv-nth 1 (rp-rw-meta-rules term meta-rules rp-state state))
                          a)
                  (rp-evl term a)))
  :hints (("Goal"
           :in-theory (e/d (RP-RW-META-RULES
                            VALID-RP-META-RULE-LISTP)
                           (evals-equal-sk
                            mv-nth
                            RP-RW-META-RULE
                            RP-META-DONT-RW
                            RP-META-FNC
                            RP-META-TRIG-FNC
                            evals-equal-sk-necc
                            valid-rp-meta-rulep-necc
                            EX-FROM-RP
                            VALID-SC
                            ALL-FALIST-CONSISTENT
                            pseudo-termp2
                            RP-META-SYNTAX-VERIFIED
                            VALID-RP-META-RULEP)))))

(in-theory (disable valid-rp-meta-rule-listp))

#|(defthm valid-rp-meta-rule-listp-implies-rule-list-2
(implies (and (valid-rp-meta-rule-listp meta-rules a state)
)
(rp-meta-valid-syntax-listp meta-rules some-term state))
:rule-classes ((:rewrite :match-free :all))
:hints (("Goal"
:in-theory
'(valid-rp-meta-rule-listp-implies-rule-list-syntaxp))))||#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;temporarry

(defthm rp-statep-rp-rw-meta-rule
  (implies (rp-statep rp-state)
           (rp-statep (mv-nth 4 (rp-rw-meta-rule term meta-rule rp-state state))))
  :hints (("Goal"
           :in-theory (e/d (rp-stat-add-to-rules-used-meta-cnt) ()))))


(defthm rp-statep-rp-rw-meta-rules
  (implies (rp-statep rp-state)
           (rp-statep (mv-nth 4 (rp-rw-meta-rules term meta-rules rp-state state))))
  :hints (("Goal"
           :in-theory (e/d (RP-RW-META-RULES) (rp-statep
                               rp-rw-meta-rule)))))
