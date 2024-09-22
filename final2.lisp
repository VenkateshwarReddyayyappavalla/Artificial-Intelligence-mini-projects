"initializing all the puzzles"


(defvar puzzle-0 #2A ((3 1 2)
                      (7 nil 5)
                      (4 6 8)))


(defvar puzzle-1 #2A ((7 2 4)
                      (5 nil 6)
                      (8 3 1)))


(defvar puzzle-2 #2A((6 7 3)
                     (1 5 2)
                     (4 nil 8)))


(defvar *puzzle-3* #2A((nil 8 6)
                       (4 1 3)
                       (7 2 5)))


(defvar *puzzle-4* #2A((7 3 4)
                       (2 5 1)
                       (6 8 nil)))


(defvar *puzzle-5* #2A((1 3 8)
                       (4 7 5)
                       (6 nil 2)))


(defvar *puzzle-6* #2A((8 7 6)
                       (5 4 3)
                       (2 1 nil)))


(defvar goal-board #2A ((nil 1 2)
                        (3 4 5)
                        (6 7 8)))

(defun get-blank-pos (board)
  (let ((rows (array-dimension board 0))
        (columns (array-dimension board 1))
        (blank-pos '()))
    (dotimes (i rows)
      (dotimes (j columns)
        (when (null (aref board i j))
          (setf blank-pos (list i j)))))
    blank-pos))

(defun possible-actions (board)
  (let ((actions '())
        (blank-pos (get-blank-pos board)))
    (destructuring-bind (blank-row blank-col) blank-pos
      (when (< blank-col (1- (array-dimension board 1)))
        (push (list blank-row (1+ blank-col) 'right) actions))
      (when (> blank-col 0)
        (push (list blank-row (1- blank-col) 'left) actions))
      (when (< blank-row (1- (array-dimension board 0)))
        (push (list (1+ blank-row) blank-col 'down) actions))
      (when (> blank-row 0)
        (push (list (1- blank-row) blank-col 'up) actions)))
    actions))

(defun result (move state)
  (let ((new-state (alexandria:copy-array state)))
    (destructuring-bind (move-row move-col direction) move
      (declare (ignore direction))
      (destructuring-bind (blank-row blank-col) (get-blank-pos state)
        (rotatef (aref new-state blank-row blank-col)
                 (aref new-state move-row move-col))))
    new-state))

(defun expand (state)
  (let ((moves (possible-actions state)))
    (values (mapcar #'(lambda (move) (result move state))
                    moves)
            moves)))

(defun depth-limited-search_1 (start target max-depth)
  (labels ((explore (node depth reached)
             (cond ((equalp (getf node :state) target)
                    (list :actions (list (getf node :move))
                          :cost (getf node :path-cost)))
                   ((or (zerop depth)
                        (member (getf node :state) reached :test #'equalp))
                    :cut)
                   (t (block search
                        (let (cut)
                          (dolist (child (multiple-value-call #'pairlis
                                           (expand (getf node :state))))
                            (let ((result (explore (list :state (car child)
                                                         :parent (getf node :state)
                                                         :move (cdr child)
                                                         :path-cost (1+ (getf node :path-cost)))
                                                   (1- depth)
                                                   (cons (getf node :state) reached))))
                              (if (eq result :cut)
                                  (setf cut t)
                                  (when (not (eq result :fail))
                                    (return-from search (list :actions (if (getf node :move)
                                                                           (cons (getf node :move)
                                                                                 (getf result :actions))
                                                                           (getf result :actions))
                                                              :cost (getf result :cost)))))))
                          (if cut :cut :fail)))))))
    (explore (list :state start :path-cost 0) max-depth ())))

(defun depth-limited-search_2 (start target max-depth)
  (labels ((cycle-exists-p (node)
             (do ((curr (getf node :parent)
                        (getf curr :parent)))
                 ((null curr))
               (when (equalp (getf node :state) (getf curr :state))
                 (return-from cycle-exists-p t)))))
    (do* ((stack nil)
          (node (list :state start :path-cost 0) (pop stack)))
         ((or (not node) (equalp (getf node :state) target))
          (if (equalp (getf node :state) target)
              (do* ((curr node (getf curr :parent))
                    (states (list (getf node :state))
                            (cons (getf curr :state) states))
                    (path (list (getf node :move))
                          (cons (getf curr :move) path)))
                   ((null (getf curr :parent))
                    (list :moves (cdr path)
                          :states states
                          :cost (getf node :path-cost))))
              :cut))
      (if (< (getf node :path-cost) max-depth)
          (dolist (child (multiple-value-call #'pairlis
                           (expand (getf node :state))))
            (let ((child-node (list :state (car child)
                                    :parent node
                                    :move (cdr child)
                                    :path-cost (1+ (getf node :path-cost)))))
              (when (not (cycle-exists-p child-node))
                (push child-node stack))))))))

(defun iterative-deepening-searching (start target)
  (do ((depth 0 (1+ depth))
       (result :cut (depth-limited-search-recursive start target depth)))
      ((not (eq result :cut)) result)))

(defun compare-states (state1 state2)
  "Check if two arrays are equal. In this scenario, compare the board state to goal state"
  (equalp state1 state2))

(defun breadth-first-search (initial-board goal-board)
  (do* ((queue (queue:make-queue))
        (node (list :state initial-board) (queue:pop queue))
        (visited (make-hash-table :test #'equal)))
       ((or (not node) (equalp (getf node :state) goal-board))
        (if (equalp (getf node :state) goal-board)
            (do* ((curr node (getf curr :parent))
                  (states (list (getf node :state))
                          (cons (getf curr :state) states))
                  (path (list (getf node :action))
                        (cons (getf curr :action) path)))
                 ((null (getf curr :parent))
                  (list :actions (cdr path)
                        :sequence states)))))
    (dolist (child (multiple-value-call #'pairlis
                     (expand (getf node :state))))
      (when (not (gethash (prin1-to-string (car child)) visited))
        (setf (gethash (prin1-to-string (car child)) visited) t)
        (queue:push (list :state (car child)
                          :parent node
                          :action (cdr child)) queue)))))




(defun a*-search (start goal heuristic-fn)
  (let ((open-queue (queue:make-queue))
        (closed-set (make-hash-table :test 'equal))
        (g-scores (make-hash-table :test 'equal))
        (f-scores (make-hash-table :test 'equal)))
    (setf (gethash (prin1-to-string start) g-scores) 0)
    (setf (gethash (prin1-to-string start) f-scores) (funcall heuristic-fn start goal))
    (queue:push (list :state start :cost (funcall heuristic-fn start goal)) open-queue)
    (loop until (queue:emptyp open-queue)
          for current-node = (queue:pop open-queue)
          for current-state = (getf current-node :state)
          do (setf (gethash (prin1-to-string current-state) closed-set) t)
          when ( compare-states current-state goal)
          do (return-from a*-search (list :path (build-path current-node)
                                          :states (getf current-node :states)))
          do (dolist (child (multiple-value-call #'pairlis
                              (expand current-state)))
               (let* ((child-state (car child))
                      (child-action (cdr child))
                      (child-g-score (1+ (gethash (prin1-to-string current-state) g-scores))))
                 (when (not (gethash (prin1-to-string child-state) closed-set))
                   (when (or (not (gethash (prin1-to-string child-state) g-scores))
                             (< child-g-score (gethash (prin1-to-string child-state) g-scores)))
                     (setf (gethash (prin1-to-string child-state) g-scores) child-g-score)
                     (setf (gethash (prin1-to-string child-state) f-scores) (+ child-g-score (funcall heuristic-fn child-state goal)))
                     (queue:push (list :state child-state
                                       :parent current-node
                                       :action child-action
                                       :states (cons child-state (getf current-node :states))
                                       :cost (+ child-g-score (funcall heuristic-fn child-state goal)))
                                 open-queue))))))))

(defun build-path (node)
  (labels ((construct (n path)
             (if (getf n :parent)
                 (construct (getf n :parent) (cons (getf n :action) path))
                 path)))
    (construct node nil)))

(defun misplaced-tiles (state goal)
  (let ((misplaced 0))
    (dotimes (row (array-dimension state 0))
      (dotimes (col (array-dimension state 1))
        (when (and (aref state row col) (not (equal (aref state row col) (aref goal row col))))
          (incf misplaced))))
    misplaced))

(defun manhattan-distance (state goal)
  (let ((distance 0))
    (dotimes (row (array-dimension state 0))
      (dotimes (col (array-dimension state 1))
        (let ((tile (aref state row col)))
          (when tile
            (dotimes (goal-row (array-dimension goal 0))
              (dotimes (goal-col (array-dimension goal 1))
                (when (equal tile (aref goal goal-row goal-col))
                  (incf distance (+ (abs (- row goal-row)) (abs (- col goal-col)))))))))))
    distance))

(defvar puzzle-2 #2A((6 7 3)
                     (1 5 2)
                     (4 nil 8)))

(defvar puzzle-3 #2A((nil 8 6)
                     (4 1 3)
                     (7 2 5)))

(defvar puzzle-4 #2A((7 3 4)
                     (2 5 1)
                     (6 8 nil)))

(defvar puzzle-5 #2A((1 3 8)
                     (4 7 5)
                     (6 nil 2)))

(defvar puzzle-6 #2A((8 7 6)
                     (5 4 3)
                     (2 1 nil)))

(defun profile-searches (puzzle)
  (format t "Profiling searches for ~A:~%" puzzle)
  (format t "Iterative Deepening Search:~%")
  (time (iterative-deepening-searching puzzle goal-board))
  (format t "~%Breadth-First Search:~%")
  (time (breadth-first-search puzzle goal-board))
  (format t "~%A* Search with Manhattan Distance Heuristic:~%")
  (time (a*-search puzzle goal-board #'manhattan-distance)))

(profile-searches puzzle-0)

(format t "A* Search with Number of Misplaced Tiles Heuristic on puzzle-2:~%")
(time (a*-search puzzle-2 goal-board #'misplaced-tiles))

(format t "~%A* Search with Manhattan Distance Heuristic on puzzle-2:~%")
(time (a*-search puzzle-2 goal-board #'manhattan-distance))

(defun profile-searches-average (puzzles)
  (let ((bfs-time 0) (bfs-expanded 0)
        (astar-time 0) (astar-expanded 0))
    (dolist (puzzle puzzles)
      (format t "Profiling searches for ~A:~%" puzzle)
      (multiple-value-bind (bfs-result bfs-expanded-result bfs-time-result)
          (time (breadth-first-search puzzle goal-board))
        (declare (ignore bfs-result))
        (incf bfs-time (or bfs-time-result 0))
        (incf bfs-expanded (or bfs-expanded-result 0)))
      (multiple-value-bind (astar-result astar-expanded-result astar-time-result)
          (time (a*-search puzzle goal-board #'manhattan-distance))
        (declare (ignore astar-result))
        (incf astar-time (or astar-time-result 0))
        (incf astar-expanded (or astar-expanded-result 0))))
    (format t "~%Average results:~%")
    (format t "Breadth-First Search:~%")
    (format t " Time: ~A~%" (/ bfs-time (length puzzles)))
    (format t " Nodes Expanded: ~A~%" (/ bfs-expanded (length puzzles)))
    (format t "A* Search with Manhattan Distance Heuristic:~%")
    (format t " Time: ~A~%" (/ astar-time (length puzzles)))
    (format t " Nodes Expanded: ~A~%" (/ astar-expanded (length puzzles)))))
