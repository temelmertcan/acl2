; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/defines" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines remove-mbe-logic/exec-from-term
  :parents (std/system)
  :short "Turn every call @('(mbe :logic a :exec b)') in a term
          into just its @(':logic') part @('a') or @(':exec') part @('b')."
  :long
  (xdoc::topstring
   (xdoc::p
    "The choice is determinated by the boolean flag,
     which is @('t') when the @(':logic') part is to be removed.")
   (xdoc::p
    "In translated terms,
     @(tsee mbe)s have the form @('(return-last 'mbe1-raw b a)').
     We turn that form into @('a') or @('b'), based on the flag."))

  (define remove-mbe-logic/exec-from-term ((term pseudo-termp)
                                           (logic? booleanp))
    :returns (new-term pseudo-termp :hyp (pseudo-termp term))
    (b* (((when (variablep term)) term)
         ((when (fquotep term)) term)
         (fn (ffn-symb term))
         (args (fargs term))
         ((when (and (eq fn 'return-last)
                     (equal (first args) '(quote mbe1-raw))))
          (remove-mbe-logic/exec-from-term (if logic?
                                               (second args)
                                             (third args))
                                           logic?))
         (new-fn (if (symbolp fn)
                     fn
                   (make-lambda (lambda-formals fn)
                                (remove-mbe-logic/exec-from-term
                                 (lambda-body fn)
                                 logic?))))
         (new-args (remove-mbe-logic/exec-from-terms args logic?)))
      (fcons-term new-fn new-args)))

  (define remove-mbe-logic/exec-from-terms ((terms pseudo-term-listp)
                                            (logic? booleanp))
    :returns (new-terms (and (pseudo-term-listp new-terms)
                             (equal (len new-terms) (len terms)))
                        :hyp (pseudo-term-listp terms))
    (b* (((when (endp terms)) nil)
         ((cons term terms) terms)
         (new-term (remove-mbe-logic/exec-from-term term logic?))
         (new-terms (remove-mbe-logic/exec-from-terms terms logic?)))
      (cons new-term new-terms))))

(define remove-mbe-logic-from-term ((term pseudo-termp))
  :returns (new-term pseudo-termp :hyp :guard)
  :parents (std/system remove-mbe-logic/exec-from-term)
  :short "Turn every call @('(mbe :logic a :exec b)') in a term
          into just its @(':exec') part @('b')."
  (remove-mbe-logic/exec-from-term term t))

(define remove-mbe-exec-from-term ((term pseudo-termp))
  :returns (new-term pseudo-termp :hyp :guard)
  :parents (std/system remove-mbe-logic/exec-from-term)
  :short "Turn every call @('(mbe :logic a :exec b)') in a term
          into just its @(':logic') part @('a')."
  (remove-mbe-logic/exec-from-term term nil))
