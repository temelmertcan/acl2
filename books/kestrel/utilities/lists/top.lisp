; List Utilities
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/xdoc/constructors" :dir :system)

(include-book "add-to-set-theorems")
(include-book "index-of-theorems")
(include-book "intersection-theorems")
(include-book "intersectp-theorems")
(include-book "last-theorems")
(include-book "len-const-theorems")
(include-book "primitive-theorems")
(include-book "rev-theorems")
(include-book "set-difference-theorems")
(include-book "set-size")
(include-book "union-theorems")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc list-utilities
  :parents (kestrel-utilities lists)
  :short "Some utilities for @(see lists)."
  :long
  (xdoc::topapp
   (xdoc::p
    "These are for lists with elements of any type,
     similarly to @(see std/lists).")
   (xdoc::p
    "These utilities may be eventually integrated into @(see std/lists).")))