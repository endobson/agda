#!/usr/bin/env racket
#lang racket/base

(require
  racket/cmdline
  racket/file
  racket/list
  racket/match
  racket/port
  racket/system
  racket/hash
  json)

(define file #f)
(command-line
  #:args (filename) (set! file filename))

(define full-path
  (path->complete-path file))

(match-define
  (list agda-out agda-in agda-pid agda-stderr agda-control)
  (process* "/usr/bin/env" "agda" "--interaction-json"))


(define (handle-response resp)
  (unless (hash-eq? resp)
    (error 'handle-response "Expected hash, Got: ~s" resp))
  (when #f
    (write resp)
    (newline))
  (match (hash-ref resp 'kind)
    ["Status" (void)]
    ["ClearRunningInfo" (void)]
    ["ClearHighlighting" (void)]
    ["InteractionPoints" (void)]
    ["RunningInfo"
     (printf "RUN: ~a" (hash-ref resp 'message))]
    ["DisplayInfo"
     (define info (hash-ref resp 'info))
     (match (hash-ref info 'kind)
       ["AllGoalsWarnings"
        (define invisible (hash-ref info 'invisibleGoals))
        (define visible (hash-ref info 'visibleGoals))
        (cond
          [(or (not (empty? invisible)) (not (empty? visible)))
           (printf "Unsolved goals:~n")
           (for ([goal invisible])
             (printf "Invisible: ~a" goal)
             (newline))
           (for ([goal visible])
             (printf "Visible: ~a" goal)
             (newline))]
          [else
           (printf "Typechecking succeeded~n")])]
       ["Error"
        (printf "Error: ~a~n" (hash-ref (hash-ref info 'error) 'message))]
       ["GoalSpecific"
        (printf "Goal Type: ~a" (hash-ref (hash-ref info 'goalInfo) 'type))]
       [kind (error 'handle-response "Unknown display info kind, Got: ~s in ~s" kind info)])]
    ["JumpToError" (void)]
    ["HighlightingInfo" (void)]
    [kind (error 'handle-response "Unknown response kind, Got: ~s in ~s" kind resp)]))

(define agda-out-thread
  (thread
    (lambda ()
      (let loop ()
        (define buffer (read-bytes-line agda-out))
        (unless (eof-object? buffer)
          (define buf (if (equal? (subbytes buffer 0 6) #"JSON> ")
                          (subbytes buffer 6)
                          buffer))
          (handle-response (bytes->jsexpr buf))
          (loop))))))

(define command
  (format "IOTCM \"~a\" None Direct (Cmd_load \"~a\" [])\n" full-path full-path))

(define (recurring-filesystem-change-evt path)
   (wrap-evt
     (filesystem-change-evt path)
     (lambda (_) (recurring-filesystem-change-evt path))))

(with-handlers ([exn:break? void])
  (define (wait-state fs-evt file-contents)
    (sync (handle-evt (read-line-evt (current-input-port))
            (lambda (line) (run-state)))
          (handle-evt fs-evt
            (lambda (evt)
              (define new-contents (file->bytes full-path))
              (if (equal? new-contents file-contents)
                  (wait-state evt new-contents)
                  (run-state evt new-contents))))))

  (define (run-state [fs-evt (recurring-filesystem-change-evt full-path)]
                     [file-contents (file->bytes full-path)])
    (write-string command agda-in)
    (flush-output agda-in)
    (wait-state fs-evt file-contents))
  (run-state))
