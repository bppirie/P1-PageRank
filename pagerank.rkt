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
  (define (h graph acc)        ;; Use helper function to iterate through graph
    (match graph               ;; Use pattern matching
      ['() (set-count acc)]    ;; If graph is empty return size of acc set
      [`((,fst ,snd) . ,tl) (if (set-member? acc fst)        ;; Check if first page has been seen
                              (if (set-member? acc snd)      ;; Check if second page has been seen
                                  (h tl acc)                 ;; If both have been seen then check the rest of the graph
                                  (h tl (set-add acc snd)))  ;; If second hasnt then add it to the set and check rest
                              (if (set-member? acc snd)      ;; Check if second page has been seen
                                  (h tl (set-add acc fst))   ;; If first hasnt then add it to the set and check rest
                                  (h tl (set-add (set-add acc fst) snd))))])) ;; If both havent then add both to set and check rest
  (h graph (set)))   ;; Call helper function with empty set

;; Takes some input graph and computes the number of links emanating
;; from page. For example, (num-links '((n0 n1) (n1 n0) (n0 n2)) 'n0)
;; should return 2, as 'n0 links to 'n1 and 'n2.
;;
;; (-> graph? symbol? nonnegative-integer?)
(define (num-links graph page)
  (define (h graph page acc)   ;; Use helper function to iterate through graph
    (match graph               ;; Use pattern matching
      ['() (set-count acc)]    ;; If graph is empty return size of acc set
      [`((,fst ,snd) . ,tl) (if (equal? fst page)                 ;; Check if first is page
                                (if (set-member? acc snd)         ;; If it is check if the page it links to is already in the set
                                  (h tl page acc)                 ;; If it is then check the rest of the graph
                                  (h tl page (set-add acc snd)))  ;; Otherwise add the page it links to and check rest
                              (h tl page acc))]))                 ;; Otherwise check the rest
  (h graph page (set)))   ;; Call helper with empty set

;; Calculates a set of pages that link to page within graph. For
;; example, (get-backlinks '((n0 n1) (n1 n2) (n0 n2)) n2) should
;; return (set 'n0 'n1).
;;
;; (-> graph? symbol? (set/c symbol?))
(define (get-backlinks graph page)
  (define (h graph page acc)   ;; Helper function to iterate through graph
    (match graph               ;; Use pattern matching
      ['() acc]                ;; If graph is empty set return set acc
      [`((,fst ,snd) . ,tl) (if (equal? snd page)                 ;; Check if its a link to page
                              (if (set-member? acc fst)           ;; If it is then check if it is already in the acc set
                                  (h tl page acc)                 ;; If it is then check the rest of the links
                                  (h tl page (set-add acc fst)))  ;; Otherwise add it to the set
                              (h tl page acc))]))                 ;; Otherwise check the rest of the links
  (h graph page (set)))        ;; Run helper function on graph with empty set as initial acc

;; Generate an initial pagerank for the input graph g. The returned
;; PageRank must satisfy pagerank?, and each value of the hash must be
;; equal to (/ 1 N), where N is the number of pages in the given
;; graph.
;; (-> graph? pagerank?)
(define (mk-initial-pagerank graph)
  (define N (num-pages graph))     ;; Set N as number of pages, will be used to set initial pagerank
  (define (h graph acc hash)       ;; Use helper function to iterate through graph
    (match graph                   ;; Pattern match graph
      ['() hash]                   ;; If graph is empty then return the hash
      [`((,fst ,snd) . ,tl) (cond [(and (set-member? acc fst) (set-member? acc snd)) (h tl acc hash)]           ;; If both pages have been seen then check rest
                                  [(set-member? acc fst) (h tl (set-add acc snd) (hash-set hash snd (/ 1 N)))]  ;; If snd hasnt been seen, add it to set & initialize its pagerank and check rest
                                  [(set-member? acc snd) (h tl (set-add acc fst) (hash-set hash fst (/ 1 N)))]  ;; If fst hasnt been seen, add it to set & initialize its pagerank and check rest
                                  [else (h tl (set-add (set-add acc fst) snd) (hash-set (hash-set hash fst (/ 1 N)) snd (/ 1 N)))])])) ;; If both havent been seen then do both above
  (h graph (set) (hash)))   ;; Call helper with emtpy set and empty hash

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
  (define N (num-pages graph))                    ;; Set N as number of pages
  (define rand (/ (- 1 d) N))                     ;; Set rand as the ratio achieved from dampening
  (define (new-rank pg)                           ;; Define function new-rank to calculate what the new rank should be
    (+ rand (* d (step-page-sum pr graph pg))))   ;; Add rand to result of step-page-sum call multiplied by dampening factor
  (define (h pr d graph acc newpr)                ;; Use helper function to iterate through graph
    (match graph
      ['() newpr]  ;; If graph is empty return the new pagerank
      [`((,fst ,snd) . ,tl) (cond [(and (set-member? acc fst) (set-member? acc snd)) (h pr d tl acc newpr)] ;; If both pages have been seen, check rest
                                  ;; If snd hasnt been seen then add it to the set and set its new pagerank in the new hash
                                  [(set-member? acc fst) (h pr d tl (set-add acc snd) (hash-set newpr snd (new-rank snd)))]
                                  ;; If fst hasnt been seen then add it to the set and set its new pagerank in the new hash
                                  [(set-member? acc snd) (h pr d tl (set-add acc fst) (hash-set newpr fst (new-rank fst)))]
                                  ;; If both havent been seen then do both of the steps above
                                  [else (h pr d tl (set-add (set-add acc fst) snd) (hash-set (hash-set newpr fst (new-rank fst)) snd (new-rank snd)))])]))
  (h pr d graph (set) pr)) ;; Call helper function on empty set and current pagerank hash


;; Define function to calculate the sum of rank the page will recieve from its backlinks
(define (step-page-sum pr graph pg)
  (define backs (set->list (get-backlinks graph pg))) ;; Save backs as a list of the page's backlinks
  (define (h pr graph pg pjs acc)    ;; Use helper function to iterate through backlinks
    (if (equal? pjs '())             ;; If backs is empty return the sum
        acc                          ;; Else add fraction of rank to be recieved from the backlink to acc and get the rest
        (h pr graph pg (cdr pjs) (+ acc (/ (hash-ref pr (car pjs)) (num-links graph (car pjs)))))))
  (h pr graph pg backs 0))  ;; Call helper function with backlik list and 0


;; Iterate PageRank until the largest change in any page's rank is
;; smaller than a specified delta.
;;
;; (-> pagerank? rational? graph? rational? pagerank?)
(define (iterate-pagerank-until pr d graph delta)
  (define newpr (step-pagerank pr d graph))           ;; Set newpr as the pagerank after one step
  (if (compare-pr pr graph newpr delta)               ;; If change in each page's rank is less than delta then return newpr
      newpr                                           ;; Else return iterate-pagerank again
      (iterate-pagerank-until newpr d graph delta)))



;; Define function to check if each page's rank is within delta difference
(define (compare-pr pr graph newpr delta)
  (define (h graph acc)      ;; Use helper function to iterate through the graph
    (match graph
      ['() #t]               ;; If graph is empty then return true
      [`((,fst ,snd) . ,tl) (cond [(and (set-member? acc fst) (set-member? acc snd)) (h tl acc)] ;; If both pages are in set, check rest
                                  ;; If snd hasnt been seen then check if its change in pagerank is less than delta and add it to the set. And result with result of the rest
                                  [(set-member? acc fst) (and (> delta (abs (- (hash-ref pr snd) (hash-ref newpr snd)))) (h tl (set-add acc snd)))]
                                  ;; If fst hasnt been seen then check if its change in pagerank is less than delta and add it to the set. And result with result of the rest
                                  [(set-member? acc snd) (and (> delta (abs (- (hash-ref pr fst) (hash-ref newpr fst)))) (h tl (set-add acc fst)))]
                                  ;; If neither page has been seen then do both steps above
                                  [else (and (> delta (abs (- (hash-ref pr fst) (hash-ref newpr fst)))) (> delta (abs (- (hash-ref pr snd) (hash-ref newpr snd)))) (h tl (set-add (set-add acc fst) snd)))])]))
  (h graph (set)))  ;; Call helper function with empty set
  

;; Given a PageRank, returns the list of pages it contains in ranked
;; order (from least-popular to most-popular) as a list. You may
;; assume that the none of the pages in the pagerank have the same
;; value (i.e., there will be no ambiguity in ranking)
;;
;; (-> pagerank? (listof symbol?))
(define (rank-pages pr)
  (define (h pr acc)     ;; Define helper function
    (if (hash-empty? pr) ;; If hash is empty then return acc list
        acc              ;; Else remove the best-page from hash and add it to the acc list then check rest of hash
        (h (hash-remove pr (best-pg pr)) (cons (best-pg pr) acc))))
  (h pr '()))   ;; Call helper with empty list


;; Define function to return page with highest rank from a pagerank hash
(define (best-pg pr)
  (define pr-list (hash->list pr)) ;; Convert pagerank hash to a list
  (car (foldl (lambda (nextelm acc) (if (> (cdr nextelm) (cdr acc)) ;; Fold over the list using a lambda that compares the ranks and keeps the higher rank
                                                nextelm             ;; returns a pair consisting of the page and its rank
                                                acc)) (car pr-list) pr-list)))
