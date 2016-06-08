;;; -*- emacs-lisp -*- $Id: pp-mode.el,v 1.1.1.1 2006-04-19 20:44:52 rbj01 Exp $
;;; to use this mode, you will need to do something along the lines of
;;; the following and have it in your .emacs file:
;;;    (setq pp-executable "<fullpath to ProofPower executable>")
;;;    (load "<fullpath to this file>")

;;; The fullpath to this file can be just the name of the file, if
;;; your elisp variable load-path includes the directory where it
;;; lives.

(require 'thingatpt)

(define-prefix-command 'pp-map)
(define-prefix-command 'pp-d-map)
(make-variable-buffer-local 'pp-buffer-name)
(make-variable-buffer-local 'pp-buffer-ready)
(set-default 'pp-buffer-ready nil)
(set-default 'pp-buffer-name nil)

(defvar pp-executable "/usr/local/ProofPower/0.9.1/bin/pp"
  "*Path-name for the ProofPower executable.")

(put 'pp-term 'end-op
     (function (lambda () (skip-chars-forward "^`"))))
(put 'pp-term 'beginning-op
     (function (lambda () (skip-chars-backward "^`"))))
(defun pp-term-at-point () (thing-at-point 'pp-term))

;;; makes buffer pp aware.  Currently this consists of no more than
;;; altering the syntax table if its major is sml-mode.
(defun make-buffer-pp-ready ()
  (if (eq major-mode 'sml-mode)
      (progn
        (modify-syntax-entry ?` "$")
        (modify-syntax-entry ?\\ "\\"))))

(defun pp-buffer-ok (string)
  "Checks a string to see if it is the name of a good HOL buffer.
In reality this comes down to checking that a buffer-name has a live
process in it."
  (and string (get-buffer-process string)
       (eq 'run
           (process-status
            (get-buffer-process string)))))

(defun ensure-pp-buffer-ok ()
  "Ensures by prompting that a HOL buffer name is OK, and returns it."
  (if (not pp-buffer-ready)
      (progn (make-buffer-pp-ready) (setq pp-buffer-ready t)))
  (if (pp-buffer-ok pp-buffer-name) pp-buffer-name
    (message
     (cond (pp-buffer-name (concat pp-buffer-name " not valid anymore."))
           (t "Please choose a HOL to attach this buffer to.")))
    (sleep-for 1)
    (setq pp-buffer-name (read-buffer "HOL buffer: " nil t))
    (while (not (pp-buffer-ok pp-buffer-name))
      (ding)
      (message "Not a valid HOL process")
      (sleep-for 1)
      (setq pp-buffer-name
            (read-buffer "HOL buffer: " nil t)))
    pp-buffer-name))


(defun is-a-then (s)
  (and s (or (string-equal s "THEN") (string-equal s "THENL"))))

(defun next-pp-lexeme-terminates-tactic ()
  (skip-syntax-forward " ")
  (or (eobp)
      (char-equal (following-char) ?,)
      (char-equal (following-char) ?=)
      (char-equal (following-char) ?\;)
      (is-a-then (word-at-point))
      (string= (word-at-point) "val")))

(defun previous-pp-lexeme-terminates-tactic ()
  (save-excursion
    (skip-chars-backward " \n\t\r")
    (or (bobp)
        (char-equal (preceding-char) ?,)
        (char-equal (preceding-char) ?=)
        (char-equal (preceding-char) ?\;)
        (and (condition-case nil
                 (progn (backward-char 1) t)
                 (error nil))
             (or (is-a-then (word-at-point))
                 (string= (word-at-point) "val"))))))

;;; returns true and moves forward a sexp if this is possible, returns nil
;;; and stays where it is otherwise
(defun my-forward-sexp ()
  (condition-case nil
      (progn (forward-sexp 1) t)
    (error nil)))
(defun my-backward-sexp()
  (condition-case nil
      (progn (backward-sexp 1) t)
    (error nil)))

(defun skip-pp-tactic-punctuation-forward ()
  (let ((last-point (point)))
    (while (progn (if (is-a-then (word-at-point)) (forward-word 1))
                  (skip-chars-forward ", \n\t\r")
                  (not (= last-point (point))))
      (setq last-point (point)))))

(defun word-before-point ()
  (save-excursion
    (condition-case nil
        (progn (backward-char 1) (word-at-point))
      (error nil))))

(defun skip-pp-tactic-punctuation-backward ()
  (let ((last-point (point)))
    (while (progn (if (is-a-then (word-before-point)) (forward-word -1))
                  (skip-chars-backward ", \n\t\t")
                  (not (= last-point (point))))
      (setq last-point (point)))))

(defun forward-pp-tactic (n)
  (interactive "p")
  ;; to start you have to get off "tactic" punctuation, i.e. whitespace,
  ;; commas and the words THEN and THENL.
  (let ((count (or n 1)))
    (cond ((> count 0)
           (while (> count 0)
             (let (moved)
               (skip-pp-tactic-punctuation-forward)
               (while (and (not (next-pp-lexeme-terminates-tactic))
                           (my-forward-sexp))
                 (setq moved t))
               (skip-chars-backward " \n\t\r")
               (setq count (- count 1))
               (if (not moved)
                   (error "No more HOL tactics at this level")))))
          ((< count 0)
           (while (< count 0)
             (let (moved)
               (skip-pp-tactic-punctuation-backward)
               (while (and (not (previous-pp-lexeme-terminates-tactic))
                           (my-backward-sexp))
                 (setq moved t))
               (skip-chars-forward " \n\t\r")
               (setq count (+ count 1))
               (if (not moved)
                   (error "No more HOL tactics at this level"))))))))

(defun backward-pp-tactic (n)
  (interactive "p")
  (forward-pp-tactic (if n (- n) -1)))

(defun mark-pp-tactic ()
  (interactive)
  (let ((bounds (bounds-of-thing-at-point 'pp-tactic)))
    (if bounds
        (progn
          (goto-char (cdr bounds))
          (push-mark (car bounds) t t))
      (ding)
      (message "No tactic at point"))))

(defun copy-region-as-pp-tactic (start end arg)
  "Send selected region to HOL process as tactic."
  (interactive "r\nP")
  (let* ((region-string (buffer-substring start end))
         (e-string (concat "goalstackLib." (if arg "expandf" "e")))
         (tactic-string
          (format "%s (%s) handle e => Raise e" e-string region-string)))
    (send-string-to-pp tactic-string)))

(defun send-string-as-pp-goal (s)
  (let ((goal-string
         (format  "goalstackLib.g `%s` handle e => Raise e" s)))
    (send-raw-string-to-pp goal-string)
    (send-raw-string-to-pp "goalstackLib.set_backup 100;")))

(defun pp-do-goal (arg)
  "Send term around point to HOL process as goal.
If prefix ARG is true, or if in transient mark mode, region is active and
the region contains no backquotes, then send region instead."
  (interactive "P")
  (let ((txt (condition-case nil
                 (buffer-substring (region-beginning) (region-end))
               (error nil))))
    (if (or (and mark-active transient-mark-mode (= (count ?\` txt) 0))
            arg)
      (send-string-as-pp-goal txt)
    (send-string-as-pp-goal (pp-term-at-point)))))


(defun copy-region-as-pp-definition (start end arg)
  "Send selected region to HOL process as definition/expression."
  (interactive "r\nP")
  (let* ((buffer-string (buffer-substring start end))
         (send-string (if arg
                         (concat "(" buffer-string ") handle e => Raise e")
                       buffer-string)))
    (send-string-to-pp send-string)))

(defun pp-name-top-theorem (string arg)
  "Name the top theorem of the goalstackLib.
With prefix argument, drop the goal afterwards."
  (interactive "sName for top theorem: \nP")
  (if (not (string= string ""))
      (send-raw-string-to-pp (format "val %s = top_thm()" string)))
  (if arg (send-raw-string-to-pp "goalstackLib.drop()")))

(defun remove-sml-comments (end)
  (let (done (start (point)))
    (while (and (not done) (re-search-forward "(\\*\\|\\*)" end t))
        (if (string= (match-string 0) "*)")
            (progn
              (delete-region (- start 2) (point))
              (setq done t))
          ;; found a comment beginning
          (if (not (remove-sml-comments end)) (setq done t))))
      (if (not done) (message "Incomplete comment in region given"))
      done))

(defun remove-pp-term (end-marker)
  (let ((start (point)))
    (if (re-search-forward "`" end-marker t)
        (delete-region (- start 1) (point))
      (message "Incomplete HOL term/quotation in region given"))))

(defun remove-pp-string (end-marker)
  (let ((start (point)))
    (if (re-search-forward "\n\\|[^\\]\"" end-marker t)
        (if (string= (match-string 0) "\n")
            (message "String literal terminated by newline - not allowed!")
          (delete-region (- start 1) (point))))))


(defun remove-sml-junk (start end)
  "Removes all sml comments, HOL terms and strings in the given region."
  (interactive "r")
  (let ((m (make-marker)))
    (set-marker m end)
    (save-excursion
      (goto-char start)
      (while (re-search-forward "(\\*\\|`\\|\"" m t)
        (cond ((string= (match-string 0) "(*") (remove-sml-comments m))
              ((string= (match-string 0) "`") (remove-pp-term m))
              ((string= (match-string 0) "\"") (remove-pp-string m))))
      (set-marker m nil))))

(defun remove-sml-lets-locals
  (start end &optional looking-for-end &optional recursing)
  "Removes all local-in-ends and let-in-ends from a region.  We assume
that the buffer has already had HOL terms, comments and strings removed."
  (interactive "r")
  (let ((m (if (not recursing) (set-marker (make-marker) end) end))
        retval)
    (if (not recursing) (goto-char start))
    (if (re-search-forward "\\blet\\b\\|\\blocal\\b\\|\\bend\\b" m t)
        (let ((declstring (match-string 0)))
          (if (or (string= declstring "let") (string= declstring "local"))
              (and
               (remove-sml-lets-locals (- (point) (length declstring)) m t t)
               (remove-sml-lets-locals start m looking-for-end t)
               (setq retval t))
            ;; found an "end"
            (if (not looking-for-end)
                (message "End without corresponding let/local")
              (delete-region start (point))
              (setq retval t))))
      ;; didn't find anything
      (if looking-for-end
          (message "Let/local without corresponding end")
        (setq retval t)))
    (if (not recursing) (set-marker m nil))
    retval))

(defun word-list-to-regexp (words)
  (mapconcat (lambda (s) (concat "\\b" s "\\b")) words "\\|"))

(setq pp-open-terminator-regexp
      (concat ";\\|"
              (word-list-to-regexp
               '("val" "fun" "in" "infix[lr]?" "open" "local"))))

(setq sml-struct-id-regexp "[A-Za-z][A-Za-z0-9_]*")

(defun send-string-to-pp (string)
  "Send a string to HOL process."
  (interactive "sString to send to HOL process: ")
  (let ((buf (ensure-pp-buffer-ok))
        (tmpbuf (generate-new-buffer "*HOL temporary*"))
        (old-mark-active mark-active))
    (save-excursion
      (set-buffer tmpbuf)
      (setq pp-buffer-name buf) ; version of this variable in tmpbuf
      (insert string)
      (goto-char (point-min))
      (remove-sml-junk (point-min) (point-max))
      (goto-char (point-min))
      ;; first thing to do is to search through buffer looking for
      ;; identifiers of form id.id.  When spotted such identifiers need
      ;; to have the first component of the name loaded.
      (while (re-search-forward (concat "\\(" sml-struct-id-regexp
                                        "\\)\\.\\w+")
                                (point-max) t)
        (pp-load-string (match-string 1)))
      ;; next thing to do is to look for open declarations
      (goto-char (point-min))
      ;; search through buffer for open declarations
      (while (re-search-forward "\\bopen\\b" (point-max) t)
        ;; point now after an open, now search forward to end of
        ;; buffer or a semi-colon, or an infix declaration or a
        ;; val or a fun or another open  (as per the regexp defined just
        ;; before this function definition
        (let ((start (point))
              (end
               (save-excursion
                 (if (re-search-forward pp-open-terminator-regexp
                                        (point-max) t)
                     (- (point) (length (match-string 0)))
                   (point-max)))))
          (pp-load-modules-in-region start end))))
    ;; then finally send the string
    (send-raw-string-to-pp string)
    (kill-buffer tmpbuf)
    ;; deactivate-mark will have likely been set by all the editting actions
    ;; in the temporary buffer.  We fix this here, thereby keeping the mark
    ;; active, if it is active.
    (if deactivate-mark (setq deactivate-mark nil))))

(defun send-raw-string-to-pp (string)
  "Sends a string in the raw to HOL.  Not for interactive use."
  (let ((buf (ensure-pp-buffer-ok)))
    (comint-send-string buf (concat string ";\n"))))

(defun pp-backup ()
  "Perform a HOL backup."
  (interactive)
  (send-raw-string-to-pp "goalstackLib.b()"))

(defun pp-print ()
  "Print the current HOL goal."
  (interactive)
  (send-raw-string-to-pp "goalstackLib.p()"))

(defun pp-interrupt ()
  "Perform a HOL interrupt."
  (interactive)
  (let ((buf (ensure-pp-buffer-ok)))
    (interrupt-process (get-buffer-process buf))))

(defun pp-recentre ()
  "Display the HOL window in such a way that it displays most text."
  (interactive)
  (ensure-pp-buffer-ok)
  (save-selected-window
    (select-window (get-buffer-window pp-buffer-name t))
    ;; (delete-other-windows)
    (raise-frame)
    (goto-char (point-max))
    (recenter -1)))

(defun pp-rotate (arg)
  "Rotate the goal stack N times.  Once by default."
  (interactive "p")
  (send-raw-string-to-pp (format "goalstackLib.r %d" arg)))

(defun pp-scroll-up (arg)
  "Scrolls the HOL window."
  (interactive "P")
  (ensure-pp-buffer-ok)
  (save-excursion
    (select-window (get-buffer-window pp-buffer-name t))
    (scroll-up arg)))

(defun pp-scroll-down (arg)
  "Scrolls the HOL window."
  (interactive "P")
  (ensure-pp-buffer-ok)
  (save-excursion
    (select-window (get-buffer-window pp-buffer-name t))
    (scroll-down arg)))

(defun pp-use-file (filename)
  "Gets HOL session to \"use\" a file."
  (interactive "fFile to use: ")
  (send-raw-string-to-pp (concat "use \"" filename "\";")))

(defun pp-load-string (s)
  "Loads the ML object file NAME.uo; checking that it isn't already loaded."
  (let* ((buf (ensure-pp-buffer-ok))
         (mys (format "%s" s)) ;; gets rid of text properties
         (commandstring
          (concat "val _ = if List.exists (fn s => s = \""
                  mys
                  "\") (Meta.loaded()) then () else "
                  "(print  \"Loading " mys
                  "\\n\"; " "Meta.load \"" mys "\");\n")))
    (comint-send-string buf commandstring)))

(defun pp-load-modules-in-region (start end)
  "Attempts to load all of the words in the region as modules."
  (interactive "rP")
  (save-excursion
    (goto-char start)
    (while (re-search-forward (concat "\\b" sml-struct-id-regexp "\\b") end t)
      (pp-load-string (match-string 0)))))

(defun pp-load-file (arg)
  "Gets HOL session to \"load\" the file at point.
If there is no filename at point, then prompt for file.  If the region
is active (in transient mark mode) and it looks like it might be a
module name or a white-space delimited list of module names, then send
region instead. With prefix ARG prompt for a file-name to load."
  (interactive "P")
  (let* ((wap (word-at-point))
         (txt (condition-case nil
                  (buffer-substring (region-beginning) (region-end))
                (error nil))))
    (cond (arg (pp-load-string (read-string "Library to load: ")))
          ((and mark-active transient-mark-mode
                (string-match (concat "^\\(\\s-*" sml-struct-id-regexp
                                      "\\)+\\s-*$") txt))
           (pp-load-modules-in-region (region-beginning) (region-end)))
          ((and wap (string-match "^\\w+$" wap)) (pp-load-string wap))
          (t (pp-load-string (read-string "Library to load: "))))))


;** pp map keys and function definitions

(defun pp (niceness database-name)
  "Runs a ProofPower session in a comint window.
With a numeric prefix argument, runs it niced to that level
or at level 10 with a bare prefix. "
  (interactive "P\nsProofPower database name:")
  (let* ((niceval (cond ((null niceness) 0)
                        ((listp niceness) 10)
                        (t (prefix-numeric-value niceness))))
         (ppname (format "ProofPower(n:%d)" niceval))
         (buf (cond ((> niceval 0)
                     (make-comint ppname "nice" nil
                                  (format "-%d" niceval)
                                  pp-executable))
                    (t (make-comint "ProofPower" pp-executable nil "-d" database-name)))))
    (setq pp-buffer-name (buffer-name buf))
    (switch-to-buffer buf)
    (setq pp-buffer-name (buffer-name buf))
    (setq comint-scroll-show-maximum-output t)))

(defun run-program (filename niceness)
  "Runs a PROGRAM in a comint window, with a given (optional) NICENESS."
  (interactive "fProgram to run: \nP")
  (let* ((niceval (cond ((null niceness) 0)
                        ((listp niceness) 10)
                        (t (prefix-numeric-value niceness))))
         (progname (format "%s(n:%d)"
                          (file-name-nondirectory filename)
                          niceval))
         (buf (cond ((> niceval 0)
                     (make-comint progname "nice" nil
                                  (format "-%d" niceval)
                                  (expand-file-name filename)))
                   (t (make-comint progname
                                   (expand-file-name filename)
                                   nil)))))
    (switch-to-buffer buf)))

(defun pp-toggle-show-types ()
  "Toggles the globals show_types variable."
  (interactive)
  (message "Toggling show_types")
  (send-raw-string-to-pp "Globals.show_types := not (!Globals.show_types)"))

(defun set-pp-executable (filename)
  "Sets the HOL executable variable to be equal to FILENAME."
  (interactive "fHOL executable: ")
  (setq pp-executable filename))

(defun pp-restart-goal ()
  "Restarts the current goal."
  (interactive)
  (send-raw-string-to-pp "goalstackLib.restart()"))

(defun pp-drop-goal ()
  "Drops the current goal."
  (interactive)
  (send-raw-string-to-pp "goalstackLib.drop()"))

(defun pp-open-string (module-name)
  "Opens HOL modules, prompting for the name of the module to load."
  (interactive "sName of module to (load and) open: ")
  (progn
    (pp-load-string module-name)
    (send-raw-string-to-pp (concat "open " module-name))))

(defun pp-db-match (tm)
  "Does a DB.match [] on the given TERM (given as a string, without quotes)."
  (interactive "sTerm to match on: ")
  (send-raw-string-to-pp (format "DB.match [] (Term`%s`)" tm)))

(define-key global-map "\M-q" 'pp-map)

(define-key pp-map "\C-c" 'pp-interrupt)
(define-key pp-map "\C-l" 'pp-recentre)
(define-key pp-map "\C-t" 'pp-toggle-show-types)
(define-key pp-map "\C-v" 'pp-scroll-up)
(define-key pp-map "\M-f" 'forward-pp-tactic)
(define-key pp-map "\M-b" 'backward-pp-tactic)
(define-key pp-map "\M-p" 'pp)
(define-key pp-map "\M-r" 'copy-region-as-pp-definition)
(define-key pp-map "\M-v" 'pp-scroll-down)
(define-key pp-map "b"    'pp-backup)
(define-key pp-map "d"    'pp-d-map)
  (define-key pp-d-map "r"  'pp-drop-goal)
  (define-key pp-d-map "m"  'pp-db-match)
(define-key pp-map "e"    'copy-region-as-pp-tactic)
(define-key pp-map "g"    'pp-do-goal)
(define-key pp-map "l"    'pp-load-file)
(define-key pp-map "n"    'pp-name-top-theorem)
(define-key pp-map "o"    'pp-open-string)
(define-key pp-map "p"    'pp-print)
(define-key pp-map "r"    'pp-rotate)
(define-key pp-map "R"    'pp-restart-goal)
(define-key pp-map "t"    'mark-pp-tactic)
(define-key pp-map "s"    'send-string-to-pp)
(define-key pp-map "u"    'pp-use-file)
