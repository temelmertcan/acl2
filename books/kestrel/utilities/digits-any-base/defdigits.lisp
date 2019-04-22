; Representation of Natural Numbers as Specific Digits in Specific Bases
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/xdoc/defxdoc-plus" :dir :system)

(include-book "core")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defdigits

  :parents (digits-any-base)

  :short
  (xdoc::topstring
   "Generate specialized versions of "
   (xdoc::seeurl
    "digits-any-base"
    "the operations to convert between natural numbers and digits")
   ", using specified recognizers and fixers for the digits.")

  :long

  (xdoc::topstring

   (xdoc::h3 "Introduction")

   (xdoc::p
    "The operations in the "
    (xdoc::seeurl
     "digits-any-base"
     "library to convert between natural numbers and digits")
    " are parameterized over the base.
     The recognizers and fixers for (lists of) digits
     are also parameterized;
     they are binary functions.")

   (xdoc::p
    "Given a specific base,
     and specific unary recognizers and fixers for
     lists of digits in that base,
     it is possible to generate systematically
     versions of the operations in the library,
     and accompanying theorems,
     that are specialized to the base (and thus are not parameterized over it)
     and that depend on those unary recognizers and fixers.
     This macro carries out this specialization.")

   (xdoc::p
    "These specialized operations,
     in combination with the unary recognizers and fixers,
     may be easier to use and reason about
     than the general operations,
     when the base is known.")

   (xdoc::h3 "General Form")

   (xdoc::codeblock
    "(defdigits name"
    "           :base ..."
    "           :digits-pred ..."
    "           :digits-fix ..."
    "           :bendian-to-nat ..."
    "           :lendian-to-nat ..."
    "           :nat-to-bendian ..."
    "           :nat-to-lendian ..."
    "           :digits-pred-hints ..."
    "           :digits-fix-hints ..."
    "           :digits-pred-guard-hints ..."
    "           :digits-fix-guard-hints ..."
    "           :digits-description ..."
    "           :parents ..."
    "           :short ..."
    "           :long ..."
    "  )")

   (xdoc::h3 "Inputs")

   (xdoc::desc
    "@('name')"
    (xdoc::p
     "A symbol that names the ensemble of specialized functions.
      This is used as the XDOC topic under which
      the XDOC topics for the generated events are put."))

   (xdoc::desc
    "@(':base')"
    (xdoc::p
     "A positive integer greater than 1 that specifies the base."))

   (xdoc::desc
    (list
     "@(':digits-pred')"
     "@(':digits-fix')")
    (xdoc::p
     "Symbols that name existing functions, or macros for inline functions,
      to be used as specializations of
      @(tsee dab-digit-listp) and @(tsee dab-digit-list-fix).")
    (xdoc::p
     "These must be part of an existing fixtype."))

   (xdoc::desc
    (list
     "@(':bendian-to-nat')"
     "@(':lendian-to-nat')"
     "@(':nat-to-bendian')"
     "@(':nat-to-lendian')")
    (xdoc::p
     "Symbols that specify the names to use for the generated functions
      (see details below)."))

   (xdoc::desc
    (list
     "@(':digits-pred-hints')"
     "@(':digits-fix-hints')"
     "@(':digits-pred-guard-hints')"
     "@(':digits-fix-guard-hints')")
    (xdoc::p
     "Hints to prove that the specialized recognizers and fixers
      are equivalent to the general ones,
      when their base argument is @('base').
      Besides the equalities of the functions,
      the guard of the recognizer must be @('t'),
      and the guard of the fixer must be the recognizer."))

   (xdoc::desc
    "@(':digits-description')"
    (xdoc::p
     "A string describing the values in @('digits-pred'),
      used in the generated documentation.
      It must start with a lowercase character
      (because it is inserted in the middle of generated senteces)
      and it must be plural
      (so that the generated sentences are grammatically correct)."))

   (xdoc::desc
    (list
     "@(':parents')"
     "@(':short')"
     "@(':long')")
    (xdoc::p
     "These, if present, are added to the XDOC topic generated for
      the ensemble of specialized functions."))

   (xdoc::h3 "Generated Events")

   (xdoc::desc
    (list
     "@('nat-to-bendian')"
     "@('nat-to-lendian')"
     "@('nat-to-bendian')"
     "@('nat-to-lendian')"
     "@('nat-to-bendian*')"
     "@('nat-to-lendian*')"
     "@('nat-to-bendian+')"
     "@('nat-to-lendian+')")
    (xdoc::p
     "Specialized versions of
      @(tsee bendian=>nat),
      @(tsee lendian=>nat),
      @(tsee nat=>bendian),
      @(tsee nat=>lendian),
      @(tsee nat=>bendian*),
      @(tsee nat=>lendian*),
      @(tsee nat=>bendian+), and
      @(tsee nat=>lendian+),
      for the specified @('base').
      The names of the first four are as specified by the respective inputs;
      the names for the second four are obtained by adding @('*') or @('+')
      after the names of the third and fourth function.
      These new functions are accompanied by theorems corresponding to
      the ones that accompany the original functions.
      These theorems, and the guards, use @('digits-pred') and @('digits-fix')
      instead of @(tsee dab-digit-listp) and @(tsee dab-digit-list-fix)."))

   (xdoc::p
    "The generated events include XDOC documentation.
     They are all under an XDOC for the ensemble,
     whose name is specified in the @('name') input.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ defdigits-implementation
  :parents (defdigits)
  :short "Implementation of @(tsee defdigits)."
  :order-subtopics t
  :default-parent t)

(define defdigits-fn (name
                      base
                      digits-pred
                      digits-fix
                      bendian-to-nat
                      lendian-to-nat
                      nat-to-bendian
                      nat-to-lendian
                      digits-pred-hints
                      digits-fix-hints
                      digits-pred-guard-hints
                      digits-fix-guard-hints
                      digits-description
                      parents
                      short
                      long
                      (wrld plist-worldp))
  :returns (event "A @(tsee maybe-pseudo-event-formp).")
  :mode :program
  :short "Event generated by @(tsee defdigits)."
  (b* (;; validate the NAME input:
       ((unless (symbolp name))
        (raise "The NAME input must be a symbol, ~
                 but it is ~x0 instead." name))
       ;; validate the :BASE input:
       ((unless (dab-basep base))
        (raise "The :BASE input must be an integer greater than 1, ~
                 but it is ~x0 instead." base))
       ;; validate the :DIGITS-PRED input:
       ((unless (symbolp digits-pred))
        (raise "The :DIGITS-PRED input must be a symbol, ~
                 but it is ~x0 instead." digits-pred))
       ((unless (or (getpropc digits-pred 'macro-args nil wrld)
                    ;; above condition says macro symbol with 1+ args
                    (function-symbolp digits-pred wrld)))
        (raise "The symbol ~x0 must name an existing function, ~
                or a macro for an inline function, ~
                but it does not." digits-pred))
       ;; validate the :DIGITS-FIX input:
       ((unless (symbolp digits-fix))
        (raise "The :DIGITS-FIX input must be a symbol, ~
                 but it is ~x0 instead." digits-fix))
       ((unless (or (getpropc digits-fix 'macro-args nil wrld)
                    ;; above condition says macro symbol with 1+ args
                    (function-symbolp digits-fix wrld)))
        (raise "The symbol ~x0 must name an existing function, ~
                or a macro for an inline function, ~
                but it does not." digits-fix))
       ;; validate the :BENDIAN-TO-NAT input:
       ((unless (symbolp bendian-to-nat))
        (raise "The :BENDIAN-TO-NAT input must be a symbol, ~
                 but it is ~x0 instead." bendian-to-nat))
       ;; validate the :LENDIAN-TO-NAT input:
       ((unless (symbolp lendian-to-nat))
        (raise "The :LENDIAN-TO-NAT input must be a symbol, ~
                 but it is ~x0 instead." lendian-to-nat))
       ;; validate the :NAT-TO-BENDIAN input:
       ((unless (symbolp nat-to-bendian))
        (raise "The :NAT-TO-BENDIAN input must be a symbol, ~
                 but it is ~x0 instead." nat-to-bendian))
       ;; validate the :NAT-TO-LENDIAN input:
       ((unless (symbolp nat-to-lendian))
        (raise "The :NAT-TO-LENDIAN input must be a symbol, ~
                 but it is ~x0 instead." nat-to-lendian))
       ;; validate the :DIGITS-DESCRIPTION input:
       ((unless (stringp digits-description))
        (raise "The :DIGITS-DESCRIPTION input must be a string, ~
                but it is ~x0 instead." digits-description))
       ;; names of the other generated functions:
       (nat-to-bendian* (add-suffix-to-fn nat-to-bendian "*"))
       (nat-to-lendian* (add-suffix-to-fn nat-to-lendian "*"))
       (nat-to-bendian+ (add-suffix-to-fn nat-to-bendian "+"))
       (nat-to-lendian+ (add-suffix-to-fn nat-to-lendian "+"))
       ;; names of the local theorems that ensure that
       ;; the specified recognizer and fixer
       ;; are correct specialized versions of the general ones:
       (digits-pred-correct (add-suffix-to-fn digits-pred "-CORRECT"))
       (digits-fix-correct (add-suffix-to-fn digits-fix "-CORRECT"))
       (digits-pred-guard-correct (add-suffix-to-fn digits-pred
                                                    "-GUARD-CORRECT"))
       (digits-fix-guard-correct (add-suffix-to-fn digits-fix
                                                   "-GUARD-CORRECT"))
       ;; names of the (non-local) generated theorems:
       (len-of-nat-to-bendian (packn-pos (list 'len-of- nat-to-bendian)
                                         nat-to-bendian))
       (len-of-nat-to-lendian (packn-pos (list 'len-of- nat-to-lendian)
                                         nat-to-lendian))
       (bendian-to-nat-of-nat-to-bendian (packn-pos (list bendian-to-nat
                                                          '-of-
                                                          nat-to-bendian)
                                                    name))
       (lendian-to-nat-of-nat-to-lendian (packn-pos (list lendian-to-nat
                                                          '-of-
                                                          nat-to-lendian)
                                                    name))
       (bendian-to-nat-of-nat-to-bendian* (packn-pos (list bendian-to-nat
                                                          '-of-
                                                           nat-to-bendian*)
                                                     name))
       (lendian-to-nat-of-nat-to-lendian* (packn-pos (list lendian-to-nat
                                                          '-of-
                                                           nat-to-lendian*)
                                                     name))
       (bendian-to-nat-of-nat-to-bendian+ (packn-pos (list bendian-to-nat
                                                          '-of-
                                                           nat-to-bendian+)
                                                     name))
       (lendian-to-nat-of-nat-to-lendian+ (packn-pos (list lendian-to-nat
                                                          '-of-
                                                           nat-to-lendian+)
                                                     name))
       (nat-to-bendian-injectivity (add-suffix-to-fn nat-to-bendian
                                                     "-INJECTIVITY"))
       (nat-to-lendian-injectivity (add-suffix-to-fn nat-to-lendian
                                                     "-INJECTIVITY"))
       (nat-to-bendian*-injectivity (add-suffix-to-fn nat-to-bendian*
                                                      "-INJECTIVITY"))
       (nat-to-lendian*-injectivity (add-suffix-to-fn nat-to-lendian*
                                                      "-INJECTIVITY"))
       (nat-to-bendian+-injectivity (add-suffix-to-fn nat-to-bendian+
                                                      "-INJECTIVITY"))
       (nat-to-lendian+-injectivity (add-suffix-to-fn nat-to-lendian+
                                                      "-INJECTIVITY"))
       (nat-to-bendian-of-bendian-to-nat (packn-pos (list nat-to-bendian
                                                          '-of-
                                                          bendian-to-nat)
                                                    name))
       (nat-to-lendian-of-lendian-to-nat (packn-pos (list nat-to-lendian
                                                          '-of-
                                                          lendian-to-nat)
                                                    name))
       (nat-to-bendian*-of-bendian-to-nat (packn-pos (list nat-to-bendian*
                                                           '-of-
                                                           bendian-to-nat)
                                                     name))
       (nat-to-lendian*-of-lendian-to-nat (packn-pos (list nat-to-lendian*
                                                           '-of-
                                                           lendian-to-nat)
                                                     name))
       (nat-to-bendian+-of-bendian-to-nat (packn-pos (list nat-to-bendian+
                                                           '-of-
                                                           bendian-to-nat)
                                                     name))
       (nat-to-lendian+-of-lendian-to-nat (packn-pos (list nat-to-lendian+
                                                           '-of-
                                                           lendian-to-nat)
                                                     name))
       (bendian-to-nat-injectivity (add-suffix-to-fn bendian-to-nat
                                                     "-INJECTIVITY"))
       (lendian-to-nat-injectivity (add-suffix-to-fn lendian-to-nat
                                                     "-INJECTIVITY"))
       (bendian-to-nat-injectivity* (add-suffix-to-fn bendian-to-nat
                                                      "-INJECTIVITY*"))
       (lendian-to-nat-injectivity* (add-suffix-to-fn lendian-to-nat
                                                      "-INJECTIVITY*"))
       (bendian-to-nat-injectivity+ (add-suffix-to-fn bendian-to-nat
                                                      "-INJECTIVITY+"))
       (lendian-to-nat-injectivity+ (add-suffix-to-fn lendian-to-nat
                                                      "-INJECTIVITY+"))
       (len-of-nat-to-bendian*-leq-width (packn-pos (list 'len-of-
                                                          nat-to-bendian*
                                                          '-leq-width)
                                                    name))
       (len-of-nat-to-lendian*-leq-width (packn-pos (list 'len-of-
                                                          nat-to-lendian*
                                                          '-leq-width)
                                                    name))
       ;; names of the variables used in the generated events:
       (x (packn-pos (list "X") name))
       (digits (packn-pos (list "DIGITS") name))
       (digits1 (packn-pos (list "DIGITS1") name))
       (digits2 (packn-pos (list "DIGITS2") name))
       (nat (packn-pos (list "NAT") name))
       (nat1 (packn-pos (list "NAT1") name))
       (nat2 (packn-pos (list "NAT2") name))
       (width (packn-pos (list "WIDTH") name))
       ;; string representation of the base,
       ;; used in the generated documentation:
       (base-string (coerce (explode-nonnegative-integer base 10 nil) 'string))
       ;; generated events:
       (digits-pred-event
        `(defruledl ,digits-pred-correct
           (equal (,digits-pred ,x)
                  (dab-digit-listp ,base ,x))
           ,@(and digits-pred-hints
                  (list :hints digits-pred-hints))))
       (digits-fix-event
        `(defruledl ,digits-fix-correct
           (equal (,digits-fix ,x)
                  (dab-digit-list-fix ,base ,x))
           ,@(and digits-fix-hints
                  (list :hints digits-fix-hints))))
       (digits-pred-guard-event
        (b* ((fn (if (function-symbolp digits-pred wrld)
                     digits-pred
                   (add-suffix-to-fn digits-pred "$INLINE"))))
          `(defrulel ,digits-pred-guard-correct
             ,(guard fn nil wrld)
             :rule-classes nil
             ,@(and digits-pred-guard-hints
                    (list :hints digits-pred-guard-hints)))))
       (digits-fix-guard-event
        (b* ((fn (if (function-symbolp digits-fix wrld)
                     digits-fix
                   (add-suffix-to-fn digits-fix "$INLINE"))))
          `(defrulel ,digits-fix-guard-correct
             (iff ,(guard fn nil wrld)
                  (,digits-pred ,(car (formals fn wrld))))
             :rule-classes nil
             ,@(and digits-fix-guard-hints
                    (list :hints digits-fix-guard-hints)))))
       (bendian-to-nat-event
        `(define ,bendian-to-nat ((,digits ,digits-pred))
           :returns (,nat natp
                          :hints (("Goal"
                                   :in-theory '(natp-of-bendian=>nat
                                                ,bendian-to-nat))))
           :parents (,name)
           :short (xdoc::topstring
                   "Convert a big-endian list of "
                   ,digits-description
                   ", seen as digits in base "
                   ,base-string
                   ", to their value.")
           (bendian=>nat ,base ,digits)
           :guard-hints (("Goal" :in-theory '(,digits-pred-correct
                                              (:e dab-basep))))
           ///
           (fty::deffixequiv ,bendian-to-nat
             :hints (("Goal"
                      :in-theory
                      '(,digits-fix-correct
                        ,bendian-to-nat
                        bendian=>nat-of-dab-digit-list-fix-digits))))))
       (lendian-to-nat-event
        `(define ,lendian-to-nat ((,digits ,digits-pred))
           :returns (,nat natp
                          :hints (("Goal"
                                   :in-theory '(natp-of-lendian=>nat
                                                ,lendian-to-nat))))
           :parents (,name)
           :short (xdoc::topstring
                   "Convert a little-endian list of "
                   ,digits-description
                   ", seen as digits in base "
                   ,base-string
                   ", to their value.")
           (lendian=>nat ,base ,digits)
           :guard-hints (("Goal" :in-theory '(,digits-pred-correct
                                              (:e dab-basep))))
           ///
           (fty::deffixequiv ,lendian-to-nat
             :hints (("Goal"
                      :in-theory
                      '(,digits-fix-correct
                        ,lendian-to-nat
                        lendian=>nat-of-dab-digit-list-fix-digits))))))
       (nat-to-bendian-event
        `(define ,nat-to-bendian ((,width natp) (,nat natp))
           :guard (< ,nat (expt ,base ,width))
           :returns (,digits ,digits-pred
                             :hints (("Goal"
                                      :in-theory
                                      '(,digits-pred-correct
                                        ,nat-to-bendian
                                        return-type-of-nat=>bendian))))
           :parents (,name)
           :short (xdoc::topstring
                   "Convert a natural number to its big-endian list of "
                   ,digits-description
                   ", seen as digits in base "
                   ,base-string
                   ", of specified length.")
           (nat=>bendian ,base ,width ,nat)
           :guard-hints (("Goal" :in-theory '((:e dab-basep))))
           ///
           (fty::deffixequiv ,nat-to-bendian
             :hints (("Goal" :in-theory '(nat=>bendian-of-nfix-width
                                          nat=>bendian-of-nfix-nat
                                          ,nat-to-bendian))))
           (defrule ,len-of-nat-to-bendian
             (equal (len (,nat-to-bendian ,width ,nat))
                    (nfix ,width))
             :in-theory '(len-of-nat=>bendian ,nat-to-bendian))))
       (nat-to-lendian-event
        `(define ,nat-to-lendian ((,width natp) (,nat natp))
           :guard (< ,nat (expt ,base ,width))
           :returns (,digits ,digits-pred
                             :hints (("Goal"
                                      :in-theory
                                      '(,digits-pred-correct
                                        ,nat-to-lendian
                                        return-type-of-nat=>lendian))))
           :parents (,name)
           :short (xdoc::topstring
                   "Convert a natural number to its little-endian list of "
                   ,digits-description
                   ", seen as digits in base "
                   ,base-string
                   ", of specified length.")
           (nat=>lendian ,base ,width ,nat)
           :guard-hints (("Goal" :in-theory '((:e dab-basep))))
           ///
           (fty::deffixequiv ,nat-to-lendian
             :hints (("Goal" :in-theory '(nat=>lendian-of-nfix-width
                                          nat=>lendian-of-nfix-nat
                                          ,nat-to-lendian))))
           (defrule ,len-of-nat-to-lendian
             (equal (len (,nat-to-lendian ,width ,nat))
                    (nfix ,width))
             :in-theory '(len-of-nat=>lendian ,nat-to-lendian))))
       (nat-to-bendian*-event
        `(define ,nat-to-bendian* ((,nat natp))
           :returns (,digits ,digits-pred
                             :hints (("Goal"
                                      :in-theory
                                      '(,digits-pred-correct
                                        ,nat-to-bendian*
                                        return-type-of-nat=>bendian*))))
           :parents (,name)
           :short (xdoc::topstring
                   "Convert a natural number to "
                   "its minimum-length big-endian list of "
                   ,digits-description
                   ", seen as sigits in base "
                   ,base-string
                   ".")
           (nat=>bendian* ,base ,nat)
           :guard-hints (("Goal" :in-theory '((:e dab-basep))))
           ///
           (fty::deffixequiv ,nat-to-bendian*
             :hints (("Goal" :in-theory '(nat=>bendian*-of-nfix-nat
                                          ,nat-to-bendian*))))))
       (nat-to-lendian*-event
        `(define ,nat-to-lendian* ((,nat natp))
           :returns (,digits ,digits-pred
                             :hints (("Goal"
                                      :in-theory
                                      '(,digits-pred-correct
                                        ,nat-to-lendian*
                                        return-type-of-nat=>lendian*))))
           :parents (,name)
           :short (xdoc::topstring
                   "Convert a natural number to "
                   "its minimum-length little-endian list of "
                   ,digits-description
                   ", seen as sigits in base "
                   ,base-string
                   ".")
           (nat=>lendian* ,base ,nat)
           :guard-hints (("Goal" :in-theory '((:e dab-basep))))
           ///
           (fty::deffixequiv ,nat-to-lendian*
             :hints (("Goal" :in-theory '(nat=>lendian*-of-nfix-nat
                                          ,nat-to-lendian*))))))
       (nat-to-bendian+-event
        `(define ,nat-to-bendian+ ((,nat natp))
           :returns (,digits ,digits-pred
                             :hints (("Goal"
                                      :in-theory
                                      '(,digits-pred-correct
                                        ,nat-to-bendian+
                                        return-type-of-nat=>bendian+))))
           :parents (,name)
           :short (xdoc::topstring
                   "Convert a natural number to "
                   "its non-empty minimum-length big-endian list of "
                   ,digits-description
                   ", seen as sigits in base "
                   ,base-string
                   ".")
           (nat=>bendian+ ,base ,nat)
           :guard-hints (("Goal" :in-theory '((:e dab-basep))))
           ///
           (fty::deffixequiv ,nat-to-bendian+
             :hints (("Goal" :in-theory '(nat=>bendian+-of-nfix-nat
                                          ,nat-to-bendian+))))))
       (nat-to-lendian+-event
        `(define ,nat-to-lendian+ ((,nat natp))
           :returns (,digits ,digits-pred
                             :hints (("Goal"
                                      :in-theory
                                      '(,digits-pred-correct
                                        ,nat-to-lendian+
                                        return-type-of-nat=>lendian+))))
           :parents (,name)
           :short (xdoc::topstring
                   "Convert a natural number to "
                   "its non-empty minimum-length little-endian list of "
                   ,digits-description
                   ", seen as sigits in base "
                   ,base-string
                   ".")
           (nat=>lendian+ ,base ,nat)
           :guard-hints (("Goal" :in-theory '((:e dab-basep))))
           ///
           (fty::deffixequiv ,nat-to-lendian+
             :hints (("Goal" :in-theory '(nat=>lendian+-of-nfix-nat
                                          ,nat-to-lendian+))))))
       (bendian-to-nat-of-nat-to-bendian-event
        `(defrule ,bendian-to-nat-of-nat-to-bendian
           :parents (,bendian-to-nat ,nat-to-bendian)
           (implies (< (nfix ,nat)
                       (expt ,base (nfix ,width)))
                    (equal (,bendian-to-nat (,nat-to-bendian ,width ,nat))
                           (nfix ,nat)))
           :in-theory '(,bendian-to-nat
                        ,nat-to-bendian
                        bendian=>nat-of-nat=>bendian
                        (:e dab-base-fix))))
       (lendian-to-nat-of-nat-to-lendian-event
        `(defrule ,lendian-to-nat-of-nat-to-lendian
           :parents (,lendian-to-nat ,nat-to-lendian)
           (implies (< (nfix ,nat)
                       (expt ,base (nfix ,width)))
                    (equal (,lendian-to-nat (,nat-to-lendian ,width ,nat))
                           (nfix ,nat)))
           :in-theory '(,lendian-to-nat
                        ,nat-to-lendian
                        lendian=>nat-of-nat=>lendian
                        (:e dab-base-fix))))
       (bendian-to-nat-of-nat-to-bendian*-event
        `(defrule ,bendian-to-nat-of-nat-to-bendian*
           :parents (,bendian-to-nat ,nat-to-bendian*)
           (equal (,bendian-to-nat (,nat-to-bendian* ,nat))
                  (nfix ,nat))
           :in-theory '(,bendian-to-nat
                        ,nat-to-bendian*
                        bendian=>nat-of-nat=>bendian*)))
       (lendian-to-nat-of-nat-to-lendian*-event
        `(defrule ,lendian-to-nat-of-nat-to-lendian*
           :parents (,lendian-to-nat ,nat-to-lendian*)
           (equal (,lendian-to-nat (,nat-to-lendian* ,nat))
                  (nfix ,nat))
           :in-theory '(,lendian-to-nat
                        ,nat-to-lendian*
                        lendian=>nat-of-nat=>lendian*)))
       (bendian-to-nat-of-nat-to-bendian+-event
        `(defrule ,bendian-to-nat-of-nat-to-bendian+
           :parents (,bendian-to-nat ,nat-to-bendian+)
           (equal (,bendian-to-nat (,nat-to-bendian+ ,nat))
                  (nfix ,nat))
           :in-theory '(,bendian-to-nat
                        ,nat-to-bendian+
                        bendian=>nat-of-nat=>bendian+)))
       (lendian-to-nat-of-nat-to-lendian+-event
        `(defrule ,lendian-to-nat-of-nat-to-lendian+
           :parents (,lendian-to-nat ,nat-to-lendian+)
           (equal (,lendian-to-nat (,nat-to-lendian+ ,nat))
                  (nfix ,nat))
           :in-theory '(,lendian-to-nat
                        ,nat-to-lendian+
                        lendian=>nat-of-nat=>lendian+)))
       (nat-to-bendian-injectivity-event
        `(defrule ,nat-to-bendian-injectivity
           :parents (,nat-to-bendian)
           (implies (and (< (nfix ,nat1)
                            (expt ,base (nfix ,width)))
                         (< (nfix ,nat2)
                            (expt ,base (nfix ,width))))
                    (equal (equal (,nat-to-bendian ,width ,nat1)
                                  (,nat-to-bendian ,width ,nat2))
                           (equal (nfix ,nat1)
                                  (nfix ,nat2))))
           :in-theory '(,nat-to-bendian
                        nat=>bendian-injectivity
                        (:e dab-base-fix))))
       (nat-to-lendian-injectivity-event
        `(defrule ,nat-to-lendian-injectivity
           :parents (,nat-to-lendian)
           (implies (and (< (nfix ,nat1)
                            (expt ,base (nfix ,width)))
                         (< (nfix ,nat2)
                            (expt ,base (nfix ,width))))
                    (equal (equal (,nat-to-lendian ,width ,nat1)
                                  (,nat-to-lendian ,width ,nat2))
                           (equal (nfix ,nat1)
                                  (nfix ,nat2))))
           :in-theory '(,nat-to-lendian
                        nat=>lendian-injectivity
                        (:e dab-base-fix))))
       (nat-to-bendian*-injectivity-event
        `(defrule ,nat-to-bendian*-injectivity
           :parents (,nat-to-bendian*)
           (equal (equal (,nat-to-bendian* ,nat1)
                         (,nat-to-bendian* ,nat2))
                  (equal (nfix ,nat1)
                         (nfix ,nat2)))
           :in-theory '(,nat-to-bendian*
                        nat=>bendian*-injectivity)))
       (nat-to-lendian*-injectivity-event
        `(defrule ,nat-to-lendian*-injectivity
           :parents (,nat-to-lendian*)
           (equal (equal (,nat-to-lendian* ,nat1)
                         (,nat-to-lendian* ,nat2))
                  (equal (nfix ,nat1)
                         (nfix ,nat2)))
           :in-theory '(,nat-to-lendian*
                        nat=>lendian*-injectivity)))
       (nat-to-bendian+-injectivity-event
        `(defrule ,nat-to-bendian+-injectivity
           :parents (,nat-to-bendian+)
           (equal (equal (,nat-to-bendian+ ,nat1)
                         (,nat-to-bendian+ ,nat2))
                  (equal (nfix ,nat1)
                         (nfix ,nat2)))
           :in-theory '(,nat-to-bendian+
                        nat=>bendian+-injectivity)))
       (nat-to-lendian+-injectivity-event
        `(defrule ,nat-to-lendian+-injectivity
           :parents (,nat-to-lendian+)
           (equal (equal (,nat-to-lendian+ ,nat1)
                         (,nat-to-lendian+ ,nat2))
                  (equal (nfix ,nat1)
                         (nfix ,nat2)))
           :in-theory '(,nat-to-lendian+
                        nat=>lendian+-injectivity)))
       (nat-to-bendian-of-bendian-to-nat-event
        `(defrule ,nat-to-bendian-of-bendian-to-nat
           :parents (,nat-to-bendian ,bendian-to-nat)
           (equal (,nat-to-bendian (len ,digits) (,bendian-to-nat ,digits))
                  (,digits-fix ,digits))
           :in-theory '(,bendian-to-nat
                        ,nat-to-bendian
                        nat=>bendian-of-bendian=>nat
                        ,digits-fix-correct)))
       (nat-to-lendian-of-lendian-to-nat-event
        `(defrule ,nat-to-lendian-of-lendian-to-nat
           :parents (,nat-to-lendian ,lendian-to-nat)
           (equal (,nat-to-lendian (len ,digits) (,lendian-to-nat ,digits))
                  (,digits-fix ,digits))
           :in-theory '(,lendian-to-nat
                        ,nat-to-lendian
                        nat=>lendian-of-lendian=>nat
                        ,digits-fix-correct)))
       (nat-to-bendian*-of-bendian-to-nat-event
        `(defrule ,nat-to-bendian*-of-bendian-to-nat
           :parents (,nat-to-bendian* ,bendian-to-nat)
           (equal (,nat-to-bendian* (,bendian-to-nat ,digits))
                  (trim-bendian* (,digits-fix ,digits)))
           :in-theory '(,bendian-to-nat
                        ,nat-to-bendian*
                        nat=>bendian*-of-bendian=>nat
                        ,digits-fix-correct)))
       (nat-to-lendian*-of-lendian-to-nat-event
        `(defrule ,nat-to-lendian*-of-lendian-to-nat
           :parents (,nat-to-lendian* ,lendian-to-nat)
           (equal (,nat-to-lendian* (,lendian-to-nat ,digits))
                  (trim-lendian* (,digits-fix ,digits)))
           :in-theory '(,lendian-to-nat
                        ,nat-to-lendian*
                        nat=>lendian*-of-lendian=>nat
                        ,digits-fix-correct)))
       (nat-to-bendian+-of-bendian-to-nat-event
        `(defrule ,nat-to-bendian+-of-bendian-to-nat
           :parents (,nat-to-bendian+ ,bendian-to-nat)
           (equal (,nat-to-bendian+ (,bendian-to-nat ,digits))
                  (trim-bendian+ (,digits-fix ,digits)))
           :in-theory '(,bendian-to-nat
                        ,nat-to-bendian+
                        nat=>bendian+-of-bendian=>nat
                        ,digits-fix-correct)))
       (nat-to-lendian+-of-lendian-to-nat-event
        `(defrule ,nat-to-lendian+-of-lendian-to-nat
           :parents (,nat-to-lendian+ ,lendian-to-nat)
           (equal (,nat-to-lendian+ (,lendian-to-nat ,digits))
                  (trim-lendian+ (,digits-fix ,digits)))
           :in-theory '(,lendian-to-nat
                        ,nat-to-lendian+
                        nat=>lendian+-of-lendian=>nat
                        ,digits-fix-correct)))
       (bendian-to-nat-injectivity-event
        `(defrule ,bendian-to-nat-injectivity
           :parents (,bendian-to-nat)
           (implies (equal (len ,digits1)
                           (len ,digits2))
                    (equal (equal (,bendian-to-nat ,digits1)
                                  (,bendian-to-nat ,digits2))
                           (equal (,digits-fix ,digits1)
                                  (,digits-fix ,digits2))))
           :in-theory '(,bendian-to-nat
                        bendian=>nat-injectivity
                        ,digits-fix-correct)))
       (lendian-to-nat-injectivity-event
        `(defrule ,lendian-to-nat-injectivity
           :parents (,lendian-to-nat)
           (implies (equal (len ,digits1)
                           (len ,digits2))
                    (equal (equal (,lendian-to-nat ,digits1)
                                  (,lendian-to-nat ,digits2))
                           (equal (,digits-fix ,digits1)
                                  (,digits-fix ,digits2))))
           :in-theory '(,lendian-to-nat
                        lendian=>nat-injectivity
                        ,digits-fix-correct)))
       (bendian-to-nat-injectivity*-event
        `(defrule ,bendian-to-nat-injectivity*
           :parents (,bendian-to-nat)
           (implies (and (equal (trim-bendian* (,digits-fix ,digits1))
                                ,digits1)
                         (equal (trim-bendian* (,digits-fix ,digits2))
                                ,digits2))
                    (equal (equal (,bendian-to-nat ,digits1)
                                  (,bendian-to-nat ,digits2))
                           (equal ,digits1 ,digits2)))
           :in-theory '(,bendian-to-nat
                        bendian=>nat-injectivity*
                        ,digits-fix-correct)))
       (lendian-to-nat-injectivity*-event
        `(defrule ,lendian-to-nat-injectivity*
           :parents (,lendian-to-nat)
           (implies (and (equal (trim-lendian* (,digits-fix ,digits1))
                                ,digits1)
                         (equal (trim-lendian* (,digits-fix ,digits2))
                                ,digits2))
                    (equal (equal (,lendian-to-nat ,digits1)
                                  (,lendian-to-nat ,digits2))
                           (equal ,digits1 ,digits2)))
           :in-theory '(,lendian-to-nat
                        lendian=>nat-injectivity*
                        ,digits-fix-correct)))
       (bendian-to-nat-injectivity+-event
        `(defrule ,bendian-to-nat-injectivity+
           :parents (,bendian-to-nat)
           (implies (and (equal (trim-bendian+ (,digits-fix ,digits1))
                                ,digits1)
                         (equal (trim-bendian+ (,digits-fix ,digits2))
                                ,digits2))
                    (equal (equal (,bendian-to-nat ,digits1)
                                  (,bendian-to-nat ,digits2))
                           (equal ,digits1 ,digits2)))
           :in-theory '(,bendian-to-nat
                        bendian=>nat-injectivity+
                        ,digits-fix-correct)))
       (lendian-to-nat-injectivity+-event
        `(defrule ,lendian-to-nat-injectivity+
           :parents (,lendian-to-nat)
           (implies (and (equal (trim-lendian+ (,digits-fix ,digits1))
                                ,digits1)
                         (equal (trim-lendian+ (,digits-fix ,digits2))
                                ,digits2))
                    (equal (equal (,lendian-to-nat ,digits1)
                                  (,lendian-to-nat ,digits2))
                           (equal ,digits1 ,digits2)))
           :in-theory '(,lendian-to-nat
                        lendian=>nat-injectivity+
                        ,digits-fix-correct)))
       (len-of-nat-to-bendian*-leq-width-event
        `(defruled ,len-of-nat-to-bendian*-leq-width
           :parents (,nat-to-bendian*)
           (implies (and (natp ,nat)
                         (natp ,width))
                    (equal (<= (len (,nat-to-bendian* ,nat))
                               ,width)
                           (< ,nat
                              (expt ,base ,width))))
           :rule-classes ((:rewrite
                           :corollary
                           (implies (and (natp ,nat)
                                         (natp ,width))
                                    (equal (> (len (,nat-to-bendian* ,nat))
                                              ,width)
                                           (>= ,nat
                                               (expt ,base ,width))))
                           :hints (("Goal" :in-theory '(not)))))
           :in-theory '(dab-basep natp ,nat-to-bendian*)
           :use (:instance len-of-nat=>bendian*-leq-width (base ,base))))
       (len-of-nat-to-lendian*-leq-width-event
        `(defruled ,len-of-nat-to-lendian*-leq-width
           :parents (,nat-to-lendian*)
           (implies (and (natp ,nat)
                         (natp ,width))
                    (equal (<= (len (,nat-to-lendian* ,nat))
                               ,width)
                           (< ,nat
                              (expt ,base ,width))))
           :rule-classes ((:rewrite
                           :corollary
                           (implies (and (natp ,nat)
                                         (natp ,width))
                                    (equal (> (len (,nat-to-lendian* ,nat))
                                              ,width)
                                           (>= ,nat
                                               (expt ,base ,width))))
                           :hints (("Goal" :in-theory '(not)))))
           :in-theory '(dab-basep natp ,nat-to-lendian*)
           :use (:instance len-of-nat=>lendian*-leq-width (base ,base))))
       (name-event
        `(defxdoc ,name
           ,@(and parents (list :parents parents))
           ,@(and short (list :short short))
           ,@(and long (list :long long)))))
    ;; top-level event:
    `(encapsulate
       ()
       (logic)
       ,digits-pred-event
       ,digits-fix-event
       ,digits-pred-guard-event
       ,digits-fix-guard-event
       (set-default-hints nil)
       (set-override-hints nil)
       ,bendian-to-nat-event
       ,lendian-to-nat-event
       ,nat-to-bendian-event
       ,nat-to-lendian-event
       ,nat-to-bendian*-event
       ,nat-to-lendian*-event
       ,nat-to-bendian+-event
       ,nat-to-lendian+-event
       ,bendian-to-nat-of-nat-to-bendian-event
       ,lendian-to-nat-of-nat-to-lendian-event
       ,bendian-to-nat-of-nat-to-bendian*-event
       ,lendian-to-nat-of-nat-to-lendian*-event
       ,bendian-to-nat-of-nat-to-bendian+-event
       ,lendian-to-nat-of-nat-to-lendian+-event
       ,nat-to-bendian-injectivity-event
       ,nat-to-lendian-injectivity-event
       ,nat-to-bendian*-injectivity-event
       ,nat-to-lendian*-injectivity-event
       ,nat-to-bendian+-injectivity-event
       ,nat-to-lendian+-injectivity-event
       ,nat-to-bendian-of-bendian-to-nat-event
       ,nat-to-lendian-of-lendian-to-nat-event
       ,nat-to-bendian*-of-bendian-to-nat-event
       ,nat-to-lendian*-of-lendian-to-nat-event
       ,nat-to-bendian+-of-bendian-to-nat-event
       ,nat-to-lendian+-of-lendian-to-nat-event
       ,bendian-to-nat-injectivity-event
       ,lendian-to-nat-injectivity-event
       ,bendian-to-nat-injectivity*-event
       ,lendian-to-nat-injectivity*-event
       ,bendian-to-nat-injectivity+-event
       ,lendian-to-nat-injectivity+-event
       ,len-of-nat-to-bendian*-leq-width-event
       ,len-of-nat-to-lendian*-leq-width-event
       ,name-event)))

(defsection defdigits-macro-definition
  :short "Definition of the @(tsee defdigits) macro."
  :long (xdoc::topstring-@def "defdigits")
  (defmacro defdigits (name
                       &key
                       base
                       digits-pred
                       digits-fix
                       bendian-to-nat
                       lendian-to-nat
                       nat-to-bendian
                       nat-to-lendian
                       digits-pred-hints
                       digits-fix-hints
                       digits-pred-guard-hints
                       digits-fix-guard-hints
                       digits-description
                       parents
                       short
                       long)
    `(make-event (defdigits-fn
                   ',name
                   ',base
                   ',digits-pred
                   ',digits-fix
                   ',bendian-to-nat
                   ',lendian-to-nat
                   ',nat-to-bendian
                   ',nat-to-lendian
                   ',digits-pred-hints
                   ',digits-fix-hints
                   ',digits-pred-guard-hints
                   ',digits-fix-guard-hints
                   ',digits-description
                   ',parents
                   ',short
                   ',long
                   (w state)))))