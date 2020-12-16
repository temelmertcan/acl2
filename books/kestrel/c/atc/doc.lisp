; C Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc atc

  :parents (c)

  :short "ATC (<b>A</b>CL2 <b>T</b>o <b>C</b>),
          a C code generator for ACL2."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "This manual page contains user-level reference documentation for ATC.
      If you are new to ATC, you should start with the "
     (xdoc::seetopic "atc-tutorial" "tutorial")
     ", which provides user-level information
      on how ATC works and how to use ATC effectively."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form

    (xdoc::codeblock
     "(atc fn1 ... fn"
     "     :const-name  ...  ; default :auto"
     "     :output-file ...  ; no default"
     "     :verbose     ...  ; default t"
     "  )"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc
     "@('fn1'), ..., @('fnp')"
     (xdoc::p
      "Names of target ACL2 functions to translate to C.")
     (xdoc::p
      "Each @('fni') must be a symbol that names a function
       that satisfies the conditions discussed in the section
       `Representation of C Code in ACL2'."))

    (xdoc::desc
     "@(':const-name') &mdash; default @(':auto')"
     (xdoc::p
      "Name of the generated ACL2 named constant
       that holds the abstract syntax tree of the generated C program.")
     (xdoc::p
      "This must be one of the following:")
     (xdoc::ul
      (xdoc::li
       "@(':auto'), to use the symbol @('*program*')
        in the @('\"C\"') package.")
      (xdoc::li
       "Any other symbol, to use as the name of the constant."))
     (xdoc::p
      "In the rest of this documentation page,
       let @('*const*') be the symbol specified by this input."))

    (xdoc::desc
     "@(':output-file') &mdash; no default"
     (xdoc::p
      "Path of the file where the generated C code goes.")
     (xdoc::p
      "This must be an ACL2 string that is a file path.
       The path may be absolute,
       or relative to
       the " (xdoc::seetopic "cbd" "current working directory") ".")
     (xdoc::p
      "The directory must exist.
       The file may or may not exist:
       if it does not exist, it is created;
       if it exists, it is overwritten.
       The file must include a @('.c') extension."))

    (xdoc::desc
     "@(':verbose') &mdash; default @('t')"
     (xdoc::p
      "Controls the amount of screen output:")
     (xdoc::ul
      (xdoc::li
       "@('t'), to show all the output.")
      (xdoc::li
       "@('nil'), to suppress all the non-error output."))))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section
    "Representation of C Code in ACL2"

    (xdoc::p
     "For now ATC supports the ACL2 representation of
      a single C translation unit (which goes into the generated file).
      This translation unit consists of one or more C function definitions.")

    (xdoc::p
     "Each C function definition is represented by
      a corresponding ACL2 function definition.
      These are the target ACL2 functions @('fni') passed as inputs.
      The order of the C functions in the translation unit is the same as
      the order of the inputs @('fn1'), ..., @('fnp').")

    (xdoc::p
     "The name of the symbol @('fni')
      must be a portable ASCII C identifier
      as defined in Section `Portable ASCII C Identifiers' below.
      The name of the symbol is used as
      the name of the corresponding C function.
      Therefore, the target functions must have all distinct symbol names;
      even if they are in different packages,
      they must have distinct symbol names
      (the package names are ignored).")

    (xdoc::p
     "The name of each symbol that is a formal parameter of each @('fni')
      must be a portable ASCII C identifier
      as defined in Section `Portable ASCII C Identifiers' below.
      The names of these symbols are used as
      the names of the formal parameters of the corresponding C function,
      in the same order.
      Therefore, the formal parameters of each @('fni')
      must have must have all distinct symbol names;
      even if they are in different packages,
      they must have distinct symbol names
      (the package names are ignored).")

    (xdoc::p
     "The guard of each @('fni') must include conjuncts of the form
      @('(sintp x)') for every formal parameter @('x').
      The conjuncts may be at any level of nesting,
      but must be easily extractable by flattening
      the @(tsee and) structure of the (translated) guard term.
      Thus, all the formal parameters of the C function represented by @('fni')
      have type @('int');
      the rest of the guard (i.e. additional requirements)
      are not explicitly represented in the C code.
      The C function returns an @('int') result;
      that this is the correct return type
      is guaranteed by the restrictions given below.")

    (xdoc::p
     "Each function @('fni') must be in logic mode and guard-verified.
      It must have an "
     (xdoc::seetopic "acl2::function-definedness" "unnormalized body")
     " consisting exclusively of
      <i>allowed non-boolean terms</i> and
      <i>allowed boolean terms</i>,
      which are inductively defined as follows:")
    (xdoc::ul
     (xdoc::li
      "The formal parameters of the function.
       These represent the corresponding C formal parameters.
       These are allowed non-boolean terms.")
     (xdoc::li
      "Calls of @(tsee sint-const) on quoted integers.
       These represent C integer constants of type @('int').
       The guard verification requirement ensures that
       the quoted integer is within the range of type @('int').
       These calls are allowed non-boolean terms.")
     (xdoc::li
      "Calls of the following functions on allowed non-boolean terms:"
      (xdoc::ul
       (xdoc::li "@(tsee sint-plus)")
       (xdoc::li "@(tsee sint-minus)")
       (xdoc::li "@(tsee sint-bitnot)")
       (xdoc::li "@(tsee sint-lognot)")
       (xdoc::li "@(tsee sint-add)")
       (xdoc::li "@(tsee sint-sub)")
       (xdoc::li "@(tsee sint-mul)")
       (xdoc::li "@(tsee sint-div)")
       (xdoc::li "@(tsee sint-rem)")
       (xdoc::li "@(tsee sint-shl-sint)")
       (xdoc::li "@(tsee sint-shr-sint)")
       (xdoc::li "@(tsee sint-lt)")
       (xdoc::li "@(tsee sint-gt)")
       (xdoc::li "@(tsee sint-le)")
       (xdoc::li "@(tsee sint-ge)")
       (xdoc::li "@(tsee sint-eq)")
       (xdoc::li "@(tsee sint-ne)")
       (xdoc::li "@(tsee sint-bitand)")
       (xdoc::li "@(tsee sint-bitxor)")
       (xdoc::li "@(tsee sint-bitior)")
       (xdoc::li "@(tsee sint-logand)")
       (xdoc::li "@(tsee sint-logor)"))
      "Each such call represents the corresponding C operator,
       applied to C @('int') values.
       The guard verification requirement ensures that
       they are always applied to values with a well-defined result,
       and that result is an @('int') value.
       If the operator is @('&&') or @('||'),
       this represents a strict (i.e. not non-strict) use of them;
       see below for how to represent non-strict uses of them,
       but the strict use is slightly simpler when usable.
       These calls are allowed non-boolean terms.")
     (xdoc::li
      "Calls of @(tsee sint01) on allowed boolean terms.
       Each such call converts an allowed boolean term
       to an allowed non-boolean term.
       These calls are allowed non-boolean terms.")
     (xdoc::li
      "Calls of @(tsee sint-nonzerop) on allowed non-boolean terms.
       Each such call converts an allowed non-boolean term
       to an allowed boolean term.
       These calls are allowed boolean terms.")
     (xdoc::li
      "Calls of @(tsee if) on
       (i) tests that are allowed boolean terms and
       (ii) branches that are allowed non-boolean terms.
       An ACL2 @(tsee if) represents
       either an C @('if') conditional statement
       or a C @('?:') conditional expression;
       the choice is explained below.
       These calls are allowed non-boolean terms.")
     (xdoc::li
      "Calls of the following functions and macros on allowed boolean terms:"
      (xdoc::ul
       (xdoc::li "@(tsee not)")
       (xdoc::li "@(tsee and)")
       (xdoc::li "@(tsee or)"))
      "The first one is a function, while the other two are macros.
       In translated terms, @('(and x y)') and @('(or x y)') are
       @('(if x y \'nil)') and @('(or x x y)'):
       these are the patterns that ATC looks for.
       Each such call represents the corresponding C logical operator
       (negation @('!'), conjunction @('&&'), disjunction @('||'));
       conjunction and disjunctions are represented non-strictly.
       These calls are allowed boolean terms.")
     (xdoc::li
      "Calls of @(tsee if) on
       (i) tests of the form @('(mbt ...)') or @('(mbt$ ...)'),
       (ii) `then' branches that are allowed non-boolean terms, and
       (iii) `else' branches that are arbitrary terms.
       Both tests and `else' branches are ignored;
       only the `then' branches represent C code and are translated to C.
       The reason is that ATC generates C code under guard assumptions.
       In translated terms,
       @('(mbt x)') is
       @('(return-last \'acl2::mbe1-raw \'t x)'), and
       @('(mbt$ x)') is
       @('(return-last \'acl2::mbe1-raw \'t (if x \'nil \'t))').")
     (xdoc::li
      "Calls of @(tsee if) on
       (i) tests of the form @('(mbt$ ...)'),
       (ii) `then' branches that are allowed non-boolean terms, and
       (iii) `else' branches that are arbitrary terms.
       Both tests and `else' branches are ignored;
       only the `then' branches represent C code and are translated to C.
       The reason is that ATC generates C code under guard assumptions.
       In translated terms, @('(mbt x)') is
       @('(return-last \'acl2::mbe1-raw \'t (if x \'nil \'t))').")
     (xdoc::li
      "Calls of a target function @('fnj'), with @('j < i'),
       on allowed non-boolean terms.
       The restriction @('j < i') means that
       no (direct or indirect) recursion is allowed
       and the target functions must be specified according to
       a topological order of their call graph."))
    (xdoc::p
     "Note that the allowed boolean terms return ACL2 boolean values,
      while the allowed non-boolean terms return ACL2 non-boolean values
      that represent C values.
      The distinction between these two kinds of allowed terms
      stems from the need to represent C's non-strictness in ACL2:
      C's non-strict constructs are
      @('if') statements,
      @('?:') expressions,
      @('&&') expressions, and
      @('||') expressions;
      C's only non-strict construct is @(tsee if)
      (which the macros @(tsee and) and @(tsee or) expand to, see above).")

    (xdoc::p
     "The above restrictions imply that @('fni') returns a single result,
      i.e. not an @(tsee mv) result.
      By construction, this result has C type @('int').")

    (xdoc::p
     "The body statement of the C function represented by each @('fni')
      is obtained by translating the ACL2 function's body as follows.
      If the body is not an @(tsee if),
      it is translated to a single C @('return') statement
      with the expression derived from the body
      according to the correspondence outlined above;
      in this case, any @(tsee if)s are turned into conditional expressions.
      If the body is an @(tsee if),
      it is turned into a C @('if') statement,
      whose test expression is derived from the ACL2 test term
      and whose branches are recursively translated
      in the same manner as the body.
      Thus, if a branch is also an @(tsee if),
      it is turned into a nested @('if') statement.
      Eventually non-@(tsee if) branches are reached,
      and they are turned into @('return') statements.
      Other calls of @(tsee if), e.g. arguments of non-@(tsee if) functions,
      are turned into C conditional expressions.
      Thus, depending on where an @(tsee if) occurs,
      it may represent either a statement or an expression,
      according to an easily predictable algorithm.")

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    (xdoc::evmac-subsection
     "Portable ASCII C Identifiers"

     (xdoc::p
      "A portable ASCII C identifier is
      a non-empty sequence of ASCII characters that:")
     (xdoc::ul
      (xdoc::li
       "Consists of only
       the 26 uppercase Latin letters,
       the 26 lowercase Latin letters,
       the 10 numeric digits,
       and the underscore.")
      (xdoc::li
       "Starts with a letter or underscore.")
      (xdoc::li
       "Differs from all the C keywords, which are"
       (xdoc::codeblock
        "auto       extern     short      while"
        "break      float      signed     _Alignas"
        "case       for        sizeof     _Alignof"
        "char       goto       static     _Atomic"
        "const      if         struct     _Bool"
        "continue   inline     switch     _Complex"
        "default    int        typedef    _Generic"
        "do         long       union      _Imaginary"
        "double     register   unsigned   _Noreturn"
        "else       restrict   void       _Static_assert"
        "enum       return     volatile   _Thread_local")))

     (xdoc::p
      "The C18 standard allows the following characters in identifiers:")
     (xdoc::ol
      (xdoc::li
       "The ten digits (but not in the starting position).
       Even though C18 does not prescribe the use of (a superset of) ASCII,
       these have obvious ASCII counterparts.")
      (xdoc::li
       "The 26 uppercase Latin letters,
       the 26 lowercase Latin letter,
       and the underscore.
       Even though C18 does not prescribe the use of (a superset of) ASCII,
       these have obvious ASCII counterparts.")
      (xdoc::li
       "Some ranges of universal characters
       (some of which cannot occur in the starting position),
       none of which are ASCII.")
      (xdoc::li
       "Other implementation-defined characters.
       These are not portable."))
     (xdoc::p
      "Thus, portable ASCII C identifiers consists of only 1 and 2 above,
      excluding 3 (non-ASCII) and 4 (non-portable).")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    (xdoc::evmac-subsection
     "Constant"

     (xdoc::p
      "ATC generates an event")
     (xdoc::codeblock
      "(defconst *const* ...)")
     (xdoc::p
      "where @('...') is the abstract syntax tree of
       the generated C translation unit,
       which ATC also pretty-prints and
       writes to the file specified by the @(':output-file') input."))

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    (xdoc::evmac-subsection
     "Theorems"

     (xdoc::p
      "ATC generates an event")
     (xdoc::codeblock
      "(defthm *const*-well-formed ...)")
     (xdoc::p
      "where @('...') is a theorem about @('*const*') stating that
       the generated (abstract syntax tree of the) translation unit
       is statically well-formed,
       i.e. it compiles according to the C18 standard.")

     (xdoc::p
      "For each target function @('fn'), ATC generates an event")
     (xdoc::codeblock
      "(defthm *const*-fn-correct ...)")
     (xdoc::p
      "where @('...') is a theorem about @('fn') and @('*const*') stating that,
       under the guard of @('fn'),
       executing the C dynamic semantics on
       the C function generated from @('fn')
       yields the same result as the function @('fn').
       That is,
       the C function is functionally equivalent to the ACL2 function.")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section
    "Generated C Code"

    (xdoc::p
     "ATC generates a single C file that contains
      a translation unit that contains
      a C function for each target ACL2 function @('fni'),
      as explained in Section `Representation of C Code in ACL2'.")

    (xdoc::p
     "The guard verification requirement stated earlier for each @('fni')
      implies that the generated C operations
      never exhibit undefined behavior,
      provided that they are called with values
      whose ACL2 counterparts satisfy the guard of @('fni').")

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    (xdoc::evmac-subsection
     "Compiling and Running the C Code"

     (xdoc::p
      "The generated C code can be compiled and run as any other C code.
       For instance, one can use @('gcc') on macOS or Linux.")

     (xdoc::p
      "Just compiling the generated C file may result in an error
       due to the lack of a @('main') function in the file.
       The code generated by ATC is meant to be called by external C code,
       where presumably a @('main') function will exist.
       To test the generated code,
       one can write a separate C file with a @('main') function
       that calls the generated functions,
       and compile both files together.
       By default, an executable @('a.out') will be generated
       (if using @('gcc') on macOS or Linux).")

     (xdoc::p
      "The directory @('[books]/kestrel/c/atc/tests')
       contains some examples of generated C code
       and handwritten C code to test it.")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section
    "Redundancy"

    (xdoc::p
     "A call of @('atc') is redundant if an only if
      it is identical to a previous successful call of @('atc')."))))
