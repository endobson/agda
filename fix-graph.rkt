#!/usr/bin/env racket
#lang racket/base

(require
  racket/port
  racket/match
  racket/set)

(define input-lines (port->lines (current-input-port)))

(define parsed-lines
  (for/list ([line input-lines])
    (match line
      ["digraph dependencies {" 'open ]
      [(regexp #px"   m(\\d+)\\[label=\"(.*?)\"\\];"
               (list orig-node id label)) `(node ,orig-node ,id ,label)]
      [(regexp #px"   m(\\d+) -> m(\\d+);"
               (list _ source target)) `(edge ,source ,target)]
      ["}" 'close ])))

(match parsed-lines
  [`(open
     (node ,orig-nodes ,node-ids ,labels) ...
     (edge ,sources ,targets) ...
     close)
    (define nodes (make-immutable-hash (map cons node-ids labels)))
    (define edges (make-hash))
    (define rev-edges (make-hash))
    (for ([id (hash-keys nodes)])
      (hash-set! edges id (mutable-set))
      (hash-set! rev-edges id (mutable-set)))

    (for ([s sources] [t targets])
      (set-add! (hash-ref edges s) t)
      (set-add! (hash-ref rev-edges t) s))


    (define root
      (match (for/list ([(t ss) rev-edges] #:when (set-empty? ss)) t)
        [(list t) t]))

    (define descendents (make-hash))
    (let compute-descendents! ([s root])
      (hash-ref! descendents s
        (lambda ()
          (apply set-union (set)
                 (hash-ref edges s)
                 (for/list ([t (hash-ref edges s)])
                   (compute-descendents! t))))))

    (define children (make-hash))
    (for ([id (hash-keys nodes)])
      (hash-set! children id
        (set-subtract
          (set-union (set) (hash-ref edges id))
          (apply set-union (set)
                 (for/list ([t (hash-ref edges id)])
                   (hash-ref descendents t))))))

    (define filtered
      (set-union
        (set root)
        ;(hash-ref children root)
        ))


    (displayln "digraph dependencies {")
    (for ([orig-node orig-nodes] [id node-ids] #:unless (set-member? filtered id))
      (displayln orig-node))
    (for* ([(s children) children] [t children] #:unless (set-member? filtered s))
      (printf "   m~a -> m~a;~n" s t))
    (displayln "}")
    ])
