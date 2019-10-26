; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "aij-notions")

(include-book "../language/primitive-values")

(include-book "kestrel/std/system/arity-plus" :dir :system)
(include-book "kestrel/std/system/function-namep" :dir :system)
(include-book "kestrel/std/system/table-alist-plus" :dir :system)
(include-book "kestrel/utilities/system/term-function-recognizers" :dir :system)
(include-book "kestrel/utilities/xdoc/defxdoc-plus" :dir :system)
(include-book "std/util/defaggregate" :dir :system)
(include-book "std/util/defenum" :dir :system)
(include-book "std/util/defval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-types
  :parents (atj-implementation)
  :short "Types used by ATJ for code generation."
  :long
  (xdoc::topstring
   (xdoc::p
    "In order to make the generated Java code more efficient and idiomatic,
     ATJ uses types that correspond to sets of ACL2 values
     and that are mapped to corresponding Java types.
     These types are used only when
     @(':deep') is @('nil') and @(':guards') is @('t').")
   (xdoc::p
    "For example, consider a unary ACL2 function
     whose guard is or implies @(tsee stringp),
     and the corresponding Java method generated by ATJ.
     Since under the assumption of guard satisfaction
     this method will always be called
     with an @('Acl2Value') that is an @('Acl2String'),
     the method can use @('Acl2String') instead of @('Acl2Value')
     as the type of the argument.
     Furthermore, suppose that, under the guard,
     the ACL2 function always returns @(tsee integerp).
     Then the Java method can use @('Acl2Integer') instead of @('Acl2Value')
     as the return type.
     In other words,
     narrower types than the one for all ACL2 values (i.e. @('Acl2Value'))
     can be used for the argument and result of this Java method.
     In future versions of ATJ,
     this narrowing can lead to methods that operate
     on Java primitive types and arrays,
     which currently ATJ does not generate.")
   (xdoc::p
    "In general, establishing the narrower input and output types
     for a Java method generated from an ACL2 function
     may involve arbitrarily hard theorem proving:
     (i) proving that the guard implies that the inputs of the ACL2 function
     satisfies the ACL2 predicates corresponding to the input types, and
     (ii) proving that the guard implies that the output of the ACL2 function
     satisfies the ACL2 predicate corresponding to the output type.
     (Currently ATJ treats ACL2 functions that return "
    (xdoc::seetopic "mv" "multiple values")
    "as if they returned one list value;
     future versions of ATJ may treat these differently,
     in which case (ii) above should be modified to
     prove the type of each result individually.)
     Since we do not want ATJ to attempt any theorem proving,
     we provide a macro @(tsee def-atj-function-type)
     to perform those theorem proving tasks
     and to record the input and output types of ACL2 functions in a table,
     and we have ATJ make use of this table.
     Note that these types are different from
     both ACL2's built-in types used for typeset reasoning
     and ACL2's tau system types.")
   (xdoc::p
    "With a table of the types of the involved ACL2 functions at hand
     (the table being constructed via calls of @(tsee def-atj-function-type)),
     ATJ performs a type analysis of the ACL2 terms in function bodies
     as it translates them to Java.
     Critically, ATJ compares
     the type inferred for the actual argument of a function
     (this type is inferred by analyzing terms recursively)
     with the type of the corresponding formal argument of the function
     (this type is retrieved from the table of function types):
     if they differ, ATJ inserts code to convert from the former to the latter,
     unless the former is a subtype of the latter in Java.
     The conversion may be a type cast,
     e.g. to convert from @('Acl2Value') to @('Acl2String');
     the cast is guaranteed to succeed,
     assuming that the ACL2 guards are verified.
     The conversion may be a change in representation,
     e.g. to convert from @('int') to @('Acl2Value');
     here the conversion is based on
     the ACL2 representation of Java @('int') values,
     described " (xdoc::seetopic "atj-primitives" "here") ".")
   (xdoc::p
    "The ATJ type information stored in the table
     determines/specifies the input and output types of the Java methods
     generated for the corresponding ACL2 functions.
     In general, there may be different choices of types possible
     for certain ACL2 functions:
     different choices will lead to slightly different Java code.
     The types of these Java methods are part of the ``API''
     that the generated Java code provides to external Java code.")
   (xdoc::p
    "The above is just an overview of the use of types by ATJ.
     More details are in the documentation of their implementation,
     and in the code generation functions that use them.")
   (xdoc::p
    "All of the above is being extended so that each ACL2 function
     may have more than one input/output type associated with it:
     (i) a main input/output type,
     provable from the guards as described above; and
     (ii) zero or more other input/output types,
     normally narrower than the main ones,
     which may be used (in the future) to generate
     possibly more efficient overloaded methods for the ACL2 function.
     For instance, AIJ already includes overloaded methods
     for ACL2's primitive arithmetic operations (@(tsee binary-+) etc.)
     that take and return narrower types than @('Acl2Number'),
     thanks to the well-known closure operations over rationals and integers
     satisfied by these operations.
     This documentation topic will be appropriately revised and extended
     when support for these additional function types,
     and their use for overloaded methods,
     is completed."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defenum atj-typep
  (:integer
   :rational
   :number
   :character
   :string
   :symbol
   :cons
   :value
   :jint)
  :short "Recognize ATJ types."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are used for code generation, as explained "
    (xdoc::seetopic "atj-types" "here")
    ".")
   (xdoc::p
    "Currently ATJ uses types corresponding to
     all the AIJ public class types for ACL2 values
     (integers, rationals, numbers,
     characters, strings, symbols,
     @(tsee cons) pairs, and all values),
     as well as a type corresponding to the Java primitive type @('int').
     More types will be added in the future.")
   (xdoc::p
    "Each ATJ type corresponds to
     (i) an ACL2 predicate (see @(tsee atj-type-predicate)) and
     (ii) a Java type (see @(tsee atj-type-to-jtype)).")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define maybe-atj-typep (x)
  :returns (yes/no booleanp)
  :short "Recognize ATJ types and @('nil')."
  (or (atj-typep x)
      (null x))
  ///

  (defrule maybe-atj-typep-when-atj-typep
    (implies (atj-typep x)
             (maybe-atj-typep x)))

  (defrule atj-type-iff-when-maybe-atj-typep
    (implies (maybe-atj-typep x)
             (iff (atj-typep x) x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist atj-type-listp (x)
  :short "Recognize true lists of ATJ types."
  (atj-typep x)
  :true-listp t
  :elementp-of-nil nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist maybe-atj-type-listp (x)
  :short "Recognize true lists of ATJ types and @('nil')s."
  (maybe-atj-typep x)
  :true-listp t
  :elementp-of-nil t
  ///
  (defrule maybe-atj-type-listp-when-atj-type-listp
    (implies (atj-type-listp x)
             (maybe-atj-type-listp x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defalist symbol-atj-type-alistp (x)
  :short "Recognize alists from symbols to ATJ types."
  :key (symbolp x)
  :val (atj-typep x)
  :true-listp t
  :keyp-of-nil t
  :valp-of-nil nil
  ///

  (defrule atj-typep-of-cdr-of-assoc-equal-when-symbol-atj-type-alistp
    (implies (symbol-atj-type-alistp alist)
             (iff (atj-typep (cdr (assoc-equal key alist)))
                  (assoc-equal key alist))))

  (defrule symbol-atj-type-alistp-of-pairlis$
    (implies (and (symbol-listp keys)
                  (atj-type-listp vals)
                  (equal (len keys) (len vals)))
             (symbol-atj-type-alistp (pairlis$ keys vals)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-subeqp ((sub atj-typep) (sup atj-typep))
  :returns (yes/no booleanp)
  :short "Partial order over ATJ types."
  :long
  (xdoc::topstring
   (xdoc::p
    "For the ATJ types that correspond to AIJ public class types,
     the subtype/supertype relationship corresponds to
     both the value subset/superset relationship in ACL2
     and the subclass/superclass relationship in AIJ.
     Furthermore, the ATJ type @(':jint') is a subtype of @(':value').
     The type @(':value') is always the top of the partial order,
     since it consists of all the ACL2 values.")
   (xdoc::p
    "To validate the definition,
     we prove that this is indeed a partial order (over the ATJ types),
     i.e. reflexive, anti-symmetric, and transitive."))
  (case sub
    (:integer (and (member-eq sup '(:integer :rational :number :value)) t))
    (:rational (and (member-eq sup '(:rational :number :value)) t))
    (:number (and (member-eq sup '(:number :value)) t))
    (:character (and (member-eq sup '(:character :value)) t))
    (:string (and (member-eq sup '(:string :value)) t))
    (:symbol (and (member-eq sup '(:symbol :value)) t))
    (:cons (and (member-eq sup '(:cons :value)) t))
    (:value (eq sup :value))
    (:jint (and (member-eq sup '(:jint :value)) t)))
  ///

  (defrule atj-type-subeqp-reflexive
    (implies (atj-typep x)
             (atj-type-subeqp x x))
    :rule-classes nil)

  (defrule atj-type-subeqp-antisymmetric
    (implies (and (atj-typep x)
                  (atj-typep y)
                  (atj-type-subeqp x y)
                  (atj-type-subeqp y x))
             (equal x y))
    :rule-classes nil)

  (defrule atj-type-subeqp-transitive
    (implies (and (atj-typep x)
                  (atj-typep y)
                  (atj-typep z)
                  (atj-type-subeqp x y)
                  (atj-type-subeqp y z))
             (atj-type-subeqp x z))
    :rule-classes nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-subp ((sub atj-typep) (sup atj-typep))
  :returns (yes/no booleanp)
  :short "Strict variant of @(tsee atj-type-subeqp)."
  (and (atj-type-subeqp sub sup)
       (not (equal sub sup))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-join ((type1 atj-typep) (type2 atj-typep))
  :returns (type atj-typep :hyp :guard)
  :short "Least upper bound of two ATJ types."
  :long
  (xdoc::topstring
   (xdoc::p
    "ATJ types form a join semilattice,
     with the partial order @(tsee atj-type-subeqp).")
   (xdoc::p
    "To validate the definition,
     we prove that the this operation indeed returns an upper bound
     that is less than or equal to any other upper bound,
     i.e. that it returns the least upper bound.")
   (xdoc::p
    "The commutativity, idempotence, and associativity of the join operation
     follows from these and the partial order properties,
     according to lattice theory."))
  (case type1
    (:character (case type2
                  (:character :character)
                  (t :value)))
    (:string (case type2
               (:string :string)
               (t :value)))
    (:symbol (case type2
               (:symbol :symbol)
               (t :value)))
    (:integer (case type2
                (:integer :integer)
                (:rational :rational)
                (:number :number)
                (t :value)))
    (:rational (case type2
                 ((:integer :rational) :rational)
                 (:number :number)
                 (t :value)))
    (:number (case type2
               ((:integer :rational :number) :number)
               (t :value)))
    (:cons (case type2
             (:cons :cons)
             (t :value)))
    (:value :value)
    (:jint (case type2
             (:jint :jint)
             (t :value))))
  ///

  (defrule atj-type-join-upper-bound
    (implies (and (atj-typep x)
                  (atj-typep y))
             (and (atj-type-subeqp x (atj-type-join x y))
                  (atj-type-subeqp y (atj-type-join x y))))
    :rule-classes nil
    :enable atj-type-subeqp)

  (defrule atj-type-join-least
    (implies (and (atj-typep x)
                  (atj-typep y)
                  (atj-typep z)
                  (atj-type-subeqp x z)
                  (atj-type-subeqp y z))
             (atj-type-subeqp (atj-type-join x y) z))
    :rule-classes nil
    :enable atj-type-subeqp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-predicate ((type atj-typep))
  :returns (pred pseudo-termfnp)
  :short "Predicate denoted by an ATJ type."
  :long
  (xdoc::topstring
   (xdoc::p
    "The predicate is the set of values denoted by the type.")
   (xdoc::p
    "The predicate for the @(':jint') type is @(tsee int-value-p),
     i.e. the model of Java @('int') values in the Java languge formalization.
     Also see " (xdoc::seetopic "atj-primitives" "here") ".")
   (xdoc::p
    "For validation, for each subtype/supertype pair
     we generate a theorem saying that
     each value satisfying the subtype's predicate
     also satisfies the supertype's predicate."))
  (case type
    (:character 'characterp)
    (:string 'stringp)
    (:symbol 'symbolp)
    (:integer 'integerp)
    (:rational 'rationalp)
    (:number 'acl2-numberp)
    (:cons 'consp)
    (:value '(lambda (_) 't))
    (:jint 'int-value-p))
  ///

  (define atj-type-predicate-gen-thm ((type1 atj-typep) (type2 atj-typep))
    (if (atj-type-subeqp type1 type2)
        `((defthm ,(packn (list 'atj-type-predicate-thm- type1 '- type2))
            (implies (,(atj-type-predicate type1) x)
                     (,(atj-type-predicate type2) x))
            :rule-classes nil))
      nil))

  (define atj-type-predicate-gen-thms-1 ((type atj-typep)
                                         (types atj-type-listp))
    (cond ((endp types) nil)
          (t (append (atj-type-predicate-gen-thm type (car types))
                     (atj-type-predicate-gen-thms-1 type (cdr types))))))

  (define atj-type-predicate-gen-thms-2 ((types1 atj-type-listp)
                                         (types2 atj-type-listp))
    (cond ((endp types1) nil)
          (t (append (atj-type-predicate-gen-thms-1 (car types1) types2)
                     (atj-type-predicate-gen-thms-2 (cdr types1) types2)))))

  (define atj-type-predicate-gen-thms ()
    (b* ((types '(:integer
                  :rational
                  :number
                  :character
                  :string
                  :symbol
                  :cons
                  :value
                  :jint)))
      `(encapsulate
         ()
         (set-ignore-ok t)
         ,@(atj-type-predicate-gen-thms-2 types types))))

  (defmacro atj-type-predicate-validate ()
    `(make-event (atj-type-predicate-gen-thms)))

  (atj-type-predicate-validate))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-types-predicates ((types atj-type-listp))
  :returns (preds pseudo-termfn-listp)
  :short "Lift @(tsee atj-type-predicate) to lists."
  (cond ((endp types) nil)
        (t (cons (atj-type-predicate (car types))
                 (atj-types-predicates (cdr types))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-to-jtype ((type atj-typep))
  :returns (jtype jtypep :hyp :guard)
  :short "Java type corresponding to an ATJ type."
  (case type
    (:character *aij-type-char*)
    (:string *aij-type-string*)
    (:symbol *aij-type-symbol*)
    (:integer *aij-type-int*)
    (:rational *aij-type-rational*)
    (:number *aij-type-number*)
    (:cons *aij-type-cons*)
    (:value *aij-type-value*)
    (:jint (jtype-int))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-types-to-jtypes ((types atj-type-listp))
  :returns (jtypes jtype-listp :hyp :guard)
  :short "Lift @(tsee atj-type-to-jtype) to lists."
  (cond ((endp types) nil)
        (t (cons (atj-type-to-jtype (car types))
                 (atj-types-to-jtypes (cdr types))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-of-value (value)
  :returns (type atj-typep)
  :short "ATJ type of an ACL2 value."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type that ATJ assigns to a quoted constant
     with the given value.
     Note that a constant like @('2') does not get type @(':jint').
     Instead, ATJ assigns @(':jint') to a term like @('(int-value 2)');
     see the code generation functions."))
  (cond ((characterp value) :character)
        ((stringp value) :string)
        ((symbolp value) :symbol)
        ((integerp value) :integer)
        ((rationalp value) :rational)
        ((acl2-numberp value) :number)
        ((consp value) :cons)
        (t :value)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defaggregate atj-function-type
  :short "Recognize ATJ function types."
  :long
  (xdoc::topstring
   (xdoc::p
    "An ATJ function type consists of
     types for the arguments (i.e. inputs)
     and a type for the result (i.e. output).
     This is like an arrow type in higher-order languages.")
   (xdoc::p
    "This may be extended in the future
     to have a list of output types instead of a single one,
     for functions that return multiple results.
     For now these functions are regarded
     as returning a single (list) result."))
  ((inputs atj-type-listp)
   (output atj-typep)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist atj-function-type-listp (x)
  :short "Recognize true lists of ATJ function types."
  (atj-function-type-p x)
  :true-listp t
  :elementp-of-nil nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defaggregate atj-function-type-info
  :short "Recognize function type information."
  :long
  (xdoc::topstring
   (xdoc::p
    "In general, each ACL2 function has, associated with it,
     a `main' function type and zero or more `other' function types,
     as mentioned in " (xdoc::seetopic "atj-types" "here") "."))
  ((main atj-function-type-p)
   (others atj-function-type-listp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-function-type-info-table-name*
  :short "Name of the table that associates ATJ types to ACL2 functions."
  'atj-function-type-info-table)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atj-function-type-info-table
  :short "Table that associates ATJ types to ACL2 functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This table is populated by
     successful calls of the @(tsee def-atj-function-type) macro."))
  (make-event
   `(table ,*atj-function-type-info-table-name* nil nil
      :guard (and (symbolp acl2::key)
                  (atj-function-type-info-p acl2::val)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-get-function-type-from-table ((fn symbolp) (wrld plist-worldp))
  :returns (fn-type atj-function-type-p)
  :short "Retrieve the main ATJ function type
          of the specified function from the table."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is retrieved from the "
    (xdoc::seetopic "atj-function-type-info-table"
                    "@(tsee def-atj-function-type) table")
    ". If the table has no entry for the function,
     a function type all consisting of @(':value') is returned.")
   (xdoc::p
    "We are not yet populating and using the other function types in the table.
     As we add more support for them, this function may need to be
     generalized to return the whole function type information,
     or renamed to reflect that it returns the main function type."))
  (b* ((table (table-alist+ *atj-function-type-info-table-name* wrld))
       (pair (assoc-eq fn table))
       ((when pair)
        (b* ((fn-info (cdr pair)))
          (if (atj-function-type-info-p fn-info)
              (atj-function-type-info->main fn-info)
            (prog2$
             (raise "Internal error: ~
                     malformed function information ~x0 for function ~x1."
                    fn-info fn)
             (atj-function-type nil :value)))))) ; unreachable
    (make-atj-function-type :inputs (repeat (arity+ fn wrld) :value)
                            :output :value))
  :prepwork
  ((defrulel consp-of-assoc-equal
     (implies (alistp alist)
              (iff (consp (assoc-equal key alist))
                   (assoc-equal key alist))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-get-function-type ((fn symbolp)
                               (guards$ booleanp)
                               (wrld plist-worldp))
  :returns (fn-type atj-function-type-p)
  :short "Obtain the main ATJ function type of the specified function."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the @(':guards') input is @('t'),
     we retrieve the type from the table
     via @(tsee atj-get-function-type-from-table).
     If the @(':guards') input is @('nil'),
     we return a function type consisting of all @(':value') types,
     because in this case types are ignored.")
   (xdoc::p
    "The discussion in @(tsee atj-get-function-type-from-table)
     about generalizing or renaming that function
     applies to this function as well."))
  (if guards$
      (atj-get-function-type-from-table fn wrld)
    (make-atj-function-type :inputs (repeat (arity+ fn wrld) :value)
                            :output :value)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define def-atj-function-type-input-theorem ((formal symbolp)
                                             (type atj-typep)
                                             (fn symbolp)
                                             (wrld plist-worldp))
  :returns (event "A @(tsee acl2::pseudo-event-formp).")
  :mode :program
  :short "Theorem generated by @(tsee def-atj-function-type)
          for an input of an ACL2 function."
  :long
  (xdoc::topstring
   (xdoc::p
    "The theorem states that, under the guard,
     the specified formal argument satisfies the predicate
     that corresponds to the specified type.")
   (xdoc::p
    "The theorem has no rule classes because its only purpose is
     to make sure that its formula holds."))
  (b* ((thm-name (packn-pos (list 'atj- fn '-input- formal '- type)
                            (pkg-witness (symbol-package-name fn))))
       (guard (guard fn nil wrld))
       (thm-formula (implicate guard
                               `(,(atj-type-predicate type) ,formal))))
    `(defthm ,thm-name
       ,(untranslate thm-formula t wrld)
       :rule-classes nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define def-atj-function-type-input-theorems ((formals symbol-listp)
                                              (types atj-type-listp)
                                              (fn symbolp)
                                              (wrld plist-worldp))
  :guard (= (len formals) (len types))
  :returns (events "A @(tsee acl2::pseudo-event-form-listp).")
  :mode :program
  :short "Theorems generated by @(tsee def-atj-function-type)
          for all the inputs of an ACL2 function."
  :long
  (xdoc::topstring
   (xdoc::p
    "This lifts @(tsee def-atj-function-type-input-theorem) to lists."))
  (if (endp formals)
      nil
    (cons (def-atj-function-type-input-theorem
            (car formals) (car types) fn wrld)
          (def-atj-function-type-input-theorems
            (cdr formals) (cdr types) fn wrld))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define def-atj-function-type-output-theorem ((type atj-typep)
                                              (fn symbolp)
                                              (wrld plist-worldp))
  :mode :program
  :returns (event "A @(tsee acl2::pseudo-event-formp).")
  :short "Theorem generated by @(tsee def-atj-function-type)
          the the output of an ACL2 function."
  :long
  (xdoc::topstring
   (xdoc::p
    "The theorem states that, under the guard,
     the function (applied to its formals) satisfies the predicate
     that corresponds to the specified type.")
   (xdoc::p
    "The theorem has no rule classes because its only purpose is
     to make sure that its formula holds."))
  (b* ((thm-name (packn-pos (list 'atj- fn '-output- type)
                            (pkg-witness (symbol-package-name fn))))
       (formals (formals fn wrld))
       (guard (guard fn nil wrld))
       (thm-formula (implicate guard
                               `(,(atj-type-predicate type)
                                 (,fn ,@formals)))))
    `(defthm ,thm-name
       ,(untranslate thm-formula t wrld)
       :rule-classes nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define def-atj-function-type-fn (fn in-tys out-ty (wrld plist-worldp))
  :returns (event "A @(tsee acl2::pseudo-event-formp).")
  :mode :program
  :short "Top-level event generated by @(tsee def-atj-function-type)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This includes the theorems for the function inputs
     and the theorem for the function output,
     as well as an event to record the function type in the table."))
  (b* (((unless (symbolp fn))
        (raise "The first input, ~x0, must be a symbol." fn))
       ((unless (atj-type-listp in-tys))
        (raise "The second input, ~x0, must be a true list of types." in-tys))
       ((unless (atj-typep out-ty))
        (raise "The third input, ~x0, must be a type." out-ty))
       (formals (formals fn wrld))
       (input-thms
        (def-atj-function-type-input-theorems formals in-tys fn wrld))
       (output-thm
        (def-atj-function-type-output-theorem out-ty fn wrld))
       (fn-ty (make-atj-function-type :inputs in-tys :output out-ty))
       (fn-info (make-atj-function-type-info :main fn-ty :others nil)))
    `(encapsulate
       ()
       (set-ignore-ok t)
       ,@input-thms
       ,output-thm
       (table ,*atj-function-type-info-table-name* ',fn ',fn-info))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection def-atj-function-type
  :short (xdoc::topstring
          "Macro to prove and record that an ACL2 function
           has certain input and output "
          (xdoc::seetopic "atj-types" "types")
          ".")
  :long
  (xdoc::topstring
   (xdoc::p
    "This has to be used on the functions of interest
     (i.e. functions for which we want to generate Java code)
     prior to calling ATJ,
     so that ATJ can take advantage of the type information
     recorded for the functions.
     This is only relevant
     when @(':deep') is @('nil') and @(':guards') is @('t');
     in all other cases, the type information is ignored.")
   (xdoc::p
    "For instance, the file @('types-for-natives.lisp') uses this macro
     on the ACL2 functions that are implemented natively in AIJ.")
   (xdoc::p
    "If ATJ encounters a function that is not in the table,
     it assumes the wider possible type (i.e. the one for all ACL2 values)
     for inputs and output of the function.
     See the code generation functions for details.")
   (xdoc::@def "def-atj-function-type"))
  (defmacro def-atj-function-type (fn in-tys out-ty)
    `(make-event (def-atj-function-type-fn ',fn ',in-tys ',out-ty (w state)))))
