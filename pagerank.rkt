#lang racket

;; Assignment 1: Implementing PageRank
;;
;; PageRank is a popular graph algorithm used for information
;; retrieval and was first popularized as an algorithm powering
;; the Google search engine. Details of the PageRank algorithm will be
;; discussed in class. Here, you will implement several functions that
;; implement the PageRank algorithm in Racket.
;;
;; Hints: 
;; 
;; - For this assignment, you may assume that no graph will include
;; any "self-links" (pages that link to themselves) and that each page
;; will link to at least one other page.
;;
;; - you can use the code in `testing-facilities.rkt` to help generate
;; test input graphs for the project. The test suite was generated
;; using those functions.
;;
;; - You may want to define "helper functions" to break up complicated
;; function definitions.

(provide graph?
         pagerank?
         num-pages
         num-links
         get-backlinks
         mk-initial-pagerank
         step-pagerank
         iterate-pagerank-until
         rank-pages)

;; This program accepts graphs as input. Graphs are represented as a
;; list of links, where each link is a list `(,src ,dst) that signals
;; page src links to page dst.
;; (-> any? boolean?)
(define (graph? glst)
  (and (list? glst)
       (andmap
        (lambda (element)
          (match element
                 [`(,(? symbol? src) ,(? symbol? dst)) #t]
                 [else #f]))
        glst)))

;; Our implementation takes input graphs and turns them into
;; PageRanks. A PageRank is a Racket hash-map that maps pages (each 
;; represented as a Racket symbol) to their corresponding weights,
;; where those weights must sum to 1 (over the whole map).
;; A PageRank encodes a discrete probability distribution over pages.
;;
;; The test graphs for this assignment adhere to several constraints:
;; + There are no "terminal" nodes. All nodes link to at least one
;; other node.
;; + There are no "self-edges," i.e., there will never be an edge `(n0
;; n0).
;; + To maintain consistenty with the last two facts, each graph will
;; have at least two nodes.
;; + There will be no "repeat" edges. I.e., if `(n0 n1) appears once
;; in the graph, it will not appear a second time.
;;
;; (-> any? boolean?)
(define (pagerank? pr)
  (and (hash? pr)
       (andmap symbol? (hash-keys pr))
       (andmap rational? (hash-values pr))
       ;; All the values in the PageRank must sum to 1. I.e., the
       ;; PageRank forms a probability distribution.
       (= 1 (foldl + 0 (hash-values pr)))))

;; Takes some input graph and computes the number of pages in the
;; graph. For example, the graph '((n0 n1) (n1 n2)) has 3 pages, n0,
;; n1, and n2.
;;
;; (-> graph? nonnegative-integer?)
(define (num-pages graph)
  (define (h graph acc)
    (match graph
      ['() (set-count acc)]
      [`((,fst ,snd) . ,tl) (if (set-member? acc fst)
                              (if (set-member? acc snd)
                                  (h tl acc)
                                  (h tl (set-add acc snd)))
                              (if (set-member? acc snd)
                                  (h tl (set-add acc fst))
                                  (h tl (set-add (set-add acc fst) snd))))]))
  (h graph (set)))

;; Takes some input graph and computes the number of links emanating
;; from page. For example, (num-links '((n0 n1) (n1 n0) (n0 n2)) 'n0)
;; should return 2, as 'n0 links to 'n1 and 'n2.
;;
;; (-> graph? symbol? nonnegative-integer?)
(define (num-links graph page)
  (define (h graph page acc)
    (match graph
      ['() (set-count acc)]
      [`((,fst ,snd) . ,tl) (if (equal? fst page)
                              (if (set-member? acc snd)
                                  (h tl page acc)
                                  (h tl page (set-add acc snd)))
                              (h tl page acc))]))
  (h graph page (set)))

;; Calculates a set of pages that link to page within graph. For
;; example, (get-backlinks '((n0 n1) (n1 n2) (n0 n2)) n2) should
;; return (set 'n0 'n1).
;;
;; (-> graph? symbol? (set/c symbol?))
(define (get-backlinks graph page)
  (define (h graph page acc)
    (match graph
      ['() acc]
      [`((,fst ,snd) . ,tl) (if (equal? snd page)
                              (if (set-member? acc fst)
                                  (h tl page acc)
                                  (h tl page (set-add acc fst)))
                              (h tl page acc))]))
  (h graph page (set)))

;; Generate an initial pagerank for the input graph g. The returned
;; PageRank must satisfy pagerank?, and each value of the hash must be
;; equal to (/ 1 N), where N is the number of pages in the given
;; graph.
;; (-> graph? pagerank?)
(define (mk-initial-pagerank graph)
  (define N (num-pages graph))
  (define (h graph acc hash)
    (match graph
      ['() hash]
      [`((,fst ,snd) . ,tl) (cond [(and (set-member? acc fst) (set-member? acc snd)) (h tl acc hash)]
                                  [(set-member? acc fst) (h tl (set-add acc snd) (hash-set hash snd (/ 1 N)))]
                                  [(set-member? acc snd) (h tl (set-add acc fst) (hash-set hash fst (/ 1 N)))]
                                  [else (h tl (set-add (set-add acc fst) snd) (hash-set (hash-set hash fst (/ 1 N)) snd (/ 1 N)))])]))
  (h graph (set) (hash)))

;; Perform one step of PageRank on the specified graph. Return a new
;; PageRank with updated values after running the PageRank
;; calculation. The next iteration's PageRank is calculated as
;;
;; NextPageRank(page-i) = (1 - d) / N + d * S
;;
;; Where:
;;  + d is a specified "dampening factor." in range [0,1]; e.g., 0.85
;;  + N is the number of pages in the graph
;;  + S is the sum of P(page-j) for all page-j.
;;  + P(page-j) is CurrentPageRank(page-j)/NumLinks(page-j)
;;  + NumLinks(page-j) is the number of outbound links of page-j
;;  (i.e., the number of pages to which page-j has links).
;;
;; (-> pagerank? rational? graph? pagerank?)
(define (step-pagerank pr d graph)
  (define N (num-pages graph))
  (define rand (/ (- 1 d) N))
  (define (new-rank pg)
    (+ rand (* d (step-page-sum pr graph pg))))
  (define (h pr d graph acc newpr)
    (match graph
      ['() newpr]
      [`((,fst ,snd) . ,tl) (cond [(and (set-member? acc fst) (set-member? acc snd)) (h pr d tl acc newpr)]
                                  [(set-member? acc fst) (h pr d tl (set-add acc snd) (hash-set newpr snd (new-rank snd)))]
                                  [(set-member? acc snd) (h pr d tl (set-add acc fst) (hash-set newpr fst (new-rank fst)))]
                                  [else (h pr d tl (set-add (set-add acc fst) snd) (hash-set (hash-set newpr fst (new-rank fst)) snd (new-rank snd)))])]))
  (h pr d graph (set) pr))

(define (step-page-sum pr graph pg)
  (define backs (set->list (get-backlinks graph pg)))
  (define (h pr graph pg pjs acc)
    (if (equal? pjs '())
        acc
        (h pr graph pg (cdr pjs) (+ acc (/ (hash-ref pr (car pjs)) (num-links graph (car pjs)))))))
  (h pr graph pg backs 0))


;; Iterate PageRank until the largest change in any page's rank is
;; smaller than a specified delta.
;;
;; (-> pagerank? rational? graph? rational? pagerank?)
(define (iterate-pagerank-until pr d graph delta)
  'todo)

;; Given a PageRank, returns the list of pages it contains in ranked
;; order (from least-popular to most-popular) as a list. You may
;; assume that the none of the pages in the pagerank have the same
;; value (i.e., there will be no ambiguity in ranking)
;;
;; (-> pagerank? (listof symbol?))
(define (rank-pages pr)
  'todo)
