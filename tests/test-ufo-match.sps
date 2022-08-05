#!/usr/bin/env scheme-script
;; -*- mode: scheme; coding: utf-8 -*- !#
;; Copyright (c) 2022 Guy Q. Schemer
;; SPDX-License-Identifier: MIT
#!r6rs

(import (rnrs (6)) (srfi :64 testing) (ufo-match))

(test-begin "test")
;;> The most notable extensions are the ability to use \emph{non-linear}
;;> patterns - patterns in which the same identifier occurs multiple
;;> times, tail patterns after ellipsis, and the experimental tree patterns.

;;> \section{Patterns}

;;> Patterns are written to look like the printed representation of
;;> the objects they match.  The basic usage is

;;> \scheme{(match expr (pat body ...) ...)}

;;> where the result of \var{expr} is matched against each pattern in
;;> turn, and the corresponding body is evaluated for the first to
;;> succeed.  Thus, a list of three elements matches a list of three
;;> elements.

;;> \example{(let ((ls (list 1 2 3))) (match ls ((1 2 3) #t)))}
(test-equal #t (let ([ls (list 1 2 3)]) (match ls ((1 2 3) #t))))

;;> If no patterns match an error is signalled.

;;> Identifiers will match anything, and make the corresponding
;;> binding available in the body.

;;> \example{(match (list 1 2 3) ((a b c) b))}
(test-equal 2 (match (list 1 2 3) ((a b c) b)))


;;> If the same identifier occurs multiple times, the first instance
;;> will match anything, but subsequent instances must match a value
;;> which is \scheme{equal?} to the first.

;;> \example{(match (list 1 2 1) ((a a b) 1) ((a b a) 2))}
(test-equal 2 (match (list 1 2 1) ((a a b) 1) ((a b a) 2)))

;;> The special identifier \scheme{_} matches anything, no matter how
;;> many times it is used, and does not bind the result in the body.

;;> \example{(match (list 1 2 1) ((_ _ b) 1) ((a b a) 2))}
(test-equal 2 (match (list 1 2 1) ((_ _ b) 1) ((a b a) 2)))

;;> To match a literal identifier (or list or any other literal), use
;;> \scheme{quote}.

;;> \example{(match 'a ('b 1) ('a 2))}
(test-equal 2  (match 'a ('b 1) ('a 2)))

;;> Analogous to its normal usage in scheme, \scheme{quasiquote} can
;;> be used to quote a mostly literally matching object with selected
;;> parts unquoted.

;;> \example|{(match (list 1 2 3) (`(1 ,b ,c) (list b c)))}|
(test-equal '(2 3)  (match (list 1 2 3) (`(1 ,b ,c) (list b c))))

;;> Often you want to match any number of a repeated pattern.  Inside
;;> a list pattern you can append \scheme{...} after an element to
;;> match zero or more of that pattern (like a regexp Kleene star).

;;> \example{(match (list 1 2) ((1 2 3 ...) #t))}
(test-equal #t (match (list 1 2) ((1 2 3 ... ) #t)))
;;> \example{(match (list 1 2 3) ((1 2 3 ...) #t))}
(test-equal #t (match (list 1 2 3) ((1 2 3 ... ) #t)))
;;> \example{(match (list 1 2 3 3 3) ((1 2 3 ...) #t))}
(test-equal #t (match (list 1 2 3 3 3) ((1 2 3 ... ) #t)))

;;> Pattern variables matched inside the repeated pattern are bound to
;;> a list of each matching instance in the body.

;;> \example{(match (list 1 2) ((a b c ...) c))}
(test-equal '() (match (list 1 2) ((a b c ... ) c)))
;;> \example{(match (list 1 2 3) ((a b c ...) c))}
(test-equal '(3) (match (list 1 2 3) ((a b c ... ) c)))
;;> \example{(match (list 1 2 3 4 5) ((a b c ...) c))}
(test-equal '(3 4 5) (match (list 1 2 3 4 5) ((a b c ... ) c)))

;;> More than one \scheme{...} may not be used in the same list, since
;;> this would require exponential backtracking in the general case.
;;> However, \scheme{...} need not be the final element in the list,
;;> and may be succeeded by a fixed number of patterns.

;;> \example{(match (list 1 2 3 4) ((a b c ... d e) c))}
(test-equal '() (match (list 1 2 3 4) ((a b c ... d e ) c)))
;;> \example{(match (list 1 2 3 4 5) ((a b c ... d e) c))}
(test-equal '(3) (match (list 1 2 3 4 5) ((a b c ... d e ) c)))
;;> \example{(match (list 1 2 3 4 5 6 7) ((a b c ... d e) c))}
(test-equal '(3 4 5) (match (list 1 2 3 4 5 6 7) ((a b c ... d e ) c)))

;;> \scheme{___} is provided as an alias for \scheme{...} when it is
;;> inconvenient to use the ellipsis (as in a syntax-rules template).

;;> The \scheme{**1} syntax is exactly like the \scheme{...} except
;;> that it matches one or more repetitions (like a regexp "+").

;;> \example{(match (list 1 2) ((a b c **1) c))}
;no matching patterns
;;> \example{(match (list 1 2 3) ((a b c **1) c))}
(test-equal '(3) (match (list 1 2 3) ((a b c **1) c)))

;;> The \scheme{*..} syntax is like \scheme{...} except that it takes
;;> two trailing integers \scheme{<n>} and \scheme{<m>}, and requires
;;> the pattern to match from \scheme{<n>} times.

;;> \example{(match (list 1 2 3) ((a b *.. 2 4) b))}
(test-equal '(2 3) (match (list 1 2 3) ((a b *.. 2 4)  b)))
;;> \example{(match (list 1 2 3 4 5 6) ((a b *.. 2 4) b))}
;no matching patterns
;;> \example{(match (list 1 2 3 4) ((a b *.. 2 4 c) c))}
(test-equal 4 (match (list 1 2 3 4 ) ((a b *.. 2 4 c)  c)))

;;> The \scheme{(<expr> =.. <n>)} syntax is a shorthand for
;;> \scheme{(<expr> *.. <n> <n>)}.

;;> \example{(match (list 1 2) ((a b =.. 2) b))}
; (test-equal '() (match (list 1 2) ((a b =.. 2)  b)))
;no matching patterns
;;> \example{(match (list 1 2 3) ((a b =.. 2) b))}
(test-equal '(2 3) (match (list 1 2 3) ((a b =.. 2)  b)))
;;> \example{(match (list 1 2 3 4) ((a b =.. 2) b))}
;no matching patterns

;;> The boolean operators \scheme{and}, \scheme{or} and \scheme{not}
;;> can be used to group and negate patterns analogously to their
;;> Scheme counterparts.

;;> The \scheme{and} operator ensures that all subpatterns match.
;;> This operator is often used with the idiom \scheme{(and x pat)} to
;;> bind \var{x} to the entire value that matches \var{pat}
;;> (c.f. "as-patterns" in ML or Haskell).  Another common use is in
;;> conjunction with \scheme{not} patterns to match a general case
;;> with certain exceptions.

;;> \example{(match 1 ((and) #t))}
(test-equal #t (match 1 ((and) #t)))
;;> \example{(match 1 ((and x) x))}
(test-equal 1 (match 1 ((and x) x)))
;;> \example{(match 1 ((and x 1) x))}
(test-equal 1 (match 1 ((and x 1) x)))

;;> The \scheme{or} operator ensures that at least one subpattern
;;> matches.  If the same identifier occurs in different subpatterns,
;;> it is matched independently.  All identifiers from all subpatterns
;;> are bound if the \scheme{or} operator matches, but the binding is
;;> only defined for identifiers from the subpattern which matched.

;;> \example{(match 1 ((or) #t) (else #f))}
(test-equal #f (match 1 ((or) #t) (else #f)))
;;> \example{(match 1 ((or x) x))}
(test-equal 1 (match 1 ((or x) x)))
;;> \example{(match 1 ((or x 2) x))}
(test-equal 1 (match 1 ((or x 2) x)))

;;> The \scheme{not} operator succeeds if the given pattern doesn't
;;> match.  None of the identifiers used are available in the body.

;;> \example{(match 1 ((not 2) #t))}
(test-equal #t (match 1 ((not 2) #t)))

;;> The more general operator \scheme{?} can be used to provide a
;;> predicate.  The usage is \scheme{(? predicate pat ...)} where
;;> \var{predicate} is a Scheme expression evaluating to a predicate
;;> called on the value to match, and any optional patterns after the
;;> predicate are then matched as in an \scheme{and} pattern.

;;> \example{(match 1 ((? odd? x) x))}
(test-equal 1 (match 1 ((? odd? x) x)))

;;> The field operator \scheme{=} is used to extract an arbitrary
;;> field and match against it.  It is useful for more complex or
;;> conditional destructuring that can't be more directly expressed in
;;> the pattern syntax.  The usage is \scheme{(= field pat)}, where
;;> \var{field} can be any expression, and should result in a
;;> procedure of one argument, which is applied to the value to match
;;> to generate a new value to match against \var{pat}.

;;> Thus the pattern \scheme{(and (= car x) (= cdr y))} is equivalent
;;> to \scheme{(x . y)}, except it will result in an immediate error
;;> if the value isn't a pair.

;;> \example{(match '(1 . 2) ((= car x) x))}
(test-equal 1 (match '(1 . 2) ((= car x) x)))
;;> \example{(match 4 ((= sqrt x) x))}
(test-equal 2 (match 4 ((= sqrt x) x)))

;;> The record operator \scheme{$} is used as a concise way to match
;;> records defined by SRFI-9 (or SRFI-99).  The usage is
;;> \scheme{(& rtd field ...)}, where \var{rtd} should be the record
;;> type descriptor specified as the first argument to
;;> \scheme{define-record-type}, and each \var{field} is a subpattern
;;> matched against the fields of the record in order.  Not all fields
;;> must be present.

;;> \example{
;;> (let ()
;;>   (define-record-type employee
;;>     (make-employee name title)
;;>     employee?
;;>     (name get-name)
;;>     (title get-title))
;;>   (match (make-employee "Bob" "Doctor")
;;>     (($ employee n t) (list t n))))
;;> }
(test-equal '("Doctor" "Bob")
    (let ()
        (define-record-type employee
            (fields 
                (immutable name)
                (immutable title)))
        (match (make-employee "Bob" "Doctor")
            (($ employee name title) (list title name)))))

;;> For records with more fields it can be helpful to match them by
;;> name rather than position.  For this you can use the \scheme{@} (and I replaced it with &)
;;> operator, originally a Gauche extension:

;;> \example{
;;> (let ()
;;>   (define-record-type employee
;;>     (make-employee name title)
;;>     employee?
;;>     (name get-name)
;;>     (title get-title))
;;>   (match (make-employee "Bob" "Doctor")
;;>     ((@ employee (title t) (name n)) (list t n))))
;;> }

(test-equal '("Doctor" "Bob")
    (let ()
        (define-record-type employee
            (fields 
                (immutable name)
                (immutable title)))
        (match (make-employee "Bob" "Doctor")
            ((& employee (name n) (title t)) (list t n)))))

;;> The \scheme{set!} and \scheme{get!} operators are used to bind an
;;> identifier to the setter and getter of a field, respectively.  The
;;> setter is a procedure of one argument, which mutates the field to
;;> that argument.  The getter is a procedure of no arguments which
;;> returns the current value of the field.

;;> \example{(let ((x (cons 1 2))) (match x ((1 . (set! s)) (s 3) x)))}
(test-equal '(1 . 3)
    (let ([x (cons 1 2)]) 
        (match x ((1 . (set! s)) (s 3) x))))
;;> \example{(match '(1 . 2) ((1 . (get! g)) (g)))}
; (test-equal 2 (match '(1 . 2) ((1 . (get! g)) (g))))

;;> The new operator \scheme{***} can be used to search a tree for
;;> subpatterns.  A pattern of the form \scheme{(x *** y)} represents
;;> the subpattern \var{y} located somewhere in a tree where the path
;;> from the current object to \var{y} can be seen as a list of the
;;> form \scheme{(x ...)}.  \var{y} can immediately match the current
;;> object in which case the path is the empty list.  In a sense it's
;;> a 2-dimensional version of the \scheme{...} pattern.

;;> As a common case the pattern \scheme{(_ *** y)} can be used to
;;> search for \var{y} anywhere in a tree, regardless of the path
;;> used.

;;> \example{(match '(a (a (a b))) ((x *** 'b) x))}
(test-equal '(a a a) (match '(a (a (a b))) ((x *** 'b) x)))
;;> \example{(match '(a (b) (c (d e) (f g))) ((x *** 'g) x))}
(test-equal '(a c f) (match '(a (b) (c (d e) (f g))) ((x *** 'g) x)))



(test-end)

(exit (if (zero? (test-runner-fail-count (test-runner-get))) 0 1))
