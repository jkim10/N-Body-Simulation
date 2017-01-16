(*Justin Kim          jkim10@wesleyan.edu*)

structure BarnesHut =
struct

  open Mechanics
  structure BB = BoundingBox
  open Plane
  open TestData

  infixr 3 ++
  infixr 4 **
  infixr 4 //
  infixr 3 -->

  datatype bhtree =
      Empty
    | Single of body
    | Cell of (Scalar.scalar * Plane.point) * BB.bbox * bhtree * bhtree * bhtree * bhtree
      (* ((mass, center), box, top-left, top-right, bottom-left, bottom-right) *)

  (* Projects the mass and center from the root node of a bhtree *)
  fun center_of_mass (T : bhtree) : Scalar.scalar * Plane.point =
      case T of
          Empty => (Scalar.zero, Plane.origin)
        | Single (m, p, _) => (m, p)
        | Cell (com, _, _,_,_,_) => com

  (* Note: Doesn't compare velocities as these are unaffected by compute_tree *)
  fun bodyEq ((m1, p1, _) : body, (m2, p2, _) : body) : bool =
      (Scalar.eq (m1, m2)) andalso Plane.pointEqual (p1, p2)

  fun bhtreeEq (t1 : bhtree, t2 : bhtree) : bool =
      case (t1, t2) of
          (Empty, Empty) => true
        | (Single b1, Single b2) => bodyEq (b1, b2)
        | (Cell ((cm1, cp1), bb1, tl1,tr1,bl1,br1), Cell ((cm2, cp2), bb2, tl2,tr2,bl2,br2)) =>
              Scalar.eq (cm1, cm2) andalso
              Plane.pointEqual (cp1, cp2) andalso
              BB.equal (bb1, bb2) andalso 
              bhtreeEq (tl1,tl2) andalso bhtreeEq (tr1,tr2) andalso 
              bhtreeEq (bl1,bl2) andalso bhtreeEq (br1,br2)
        | (_, _) => false

  (* ---------------------------------------------------------------------- *)
  (* TASKS *)

  (* TASK *)
  (* Compute the barycenter of four points.
     Assumes that all points have nonnegative mass, and 
     that at least one point has strictly positive mass. *)
  fun barycenter ((m1,p1) : (Scalar.scalar * Plane.point),
                  (m2,p2) : (Scalar.scalar * Plane.point),
                  (m3,p3) : (Scalar.scalar * Plane.point),
                  (m4,p4) : (Scalar.scalar * Plane.point)) : Scalar.scalar * Plane.point =
      let val tmass = Scalar.plus(Scalar.plus(Scalar.plus(m1,m2),m3),m4)
          val inverse = Scalar.divide(Scalar.fromRatio(1,1),tmass)
          val mr1 = (origin-->p1)**m1
          val mr2 = (origin-->p2)**m2
          val mr3 = (origin-->p3)**m3
          val mr4 = (origin-->p4)**m4
          val fvec = head((mr1++mr2++mr3++mr4)**inverse)
        in
          (tmass,fvec)
        end

  (* TASK *)
  (* Compute the four quadrants of the bounding box *)
  fun quarters (bb : BB.bbox) : BB.bbox * BB.bbox * BB.bbox * BB.bbox =
      let
        val (tl,tr,bl,br) = BB.corners(bb)
        val center = BB.center(bb)
      in
        (BB.from2Points(tl,center),
          BB.from2Points(tr,center), 
          BB.from2Points(bl,center), 
          BB.from2Points(br,center))
      end


  val true = let val (tl,tr,bl,br) = quarters(bb4) 
             in BB.equal(tl,bb0) andalso BB.equal(tr,bb1) andalso
                BB.equal(bl, bb2) andalso BB.equal(br,bb3)
             end

  (* TASK *)
  (* Computes the Barnes-Hut tree for the bodies in the given sequence.
   * Assumes all the bodies are contained in the given bounding box,
     and that no two bodies have collided (or are so close that dividing the 
     bounding box will not eventually separate them).
     *)
  fun compute_tree (s : body Seq.seq) (bb : BB.bbox) : bhtree = 
            case Seq.length(s) of
                    0 => Empty
                  | 1 => Single(Seq.nth 0 s)
                  | _ => (let val (tl,tr,bl,br) = quarters(bb)
                              val extl = (false, false, false, false)
                              val extr = (true, false, false, false)
                              val exbl = (false, false, true, false)
                              val exbr = (true, false, true, false)
                              val sortSeqtl = compute_tree (Seq.filter (fn (m,p,v) => BB.contained extl (p,tl)) s) tl
                              val sortSeqtr = compute_tree (Seq.filter (fn (m,p,v) => BB.contained extr (p,tr)) s) tr
                              val sortSeqbl = compute_tree (Seq.filter (fn (m,p,v) => BB.contained exbl (p,bl)) s) bl
                              val sortSeqbr = compute_tree (Seq.filter (fn (m,p,v) => BB.contained exbr (p,br)) s) br
                              val bc = barycenter(center_of_mass(sortSeqtl),center_of_mass(sortSeqtr),center_of_mass(sortSeqbl),center_of_mass(sortSeqbr))
                            in
                              Cell(bc, bb, sortSeqtl, sortSeqtr, sortSeqbl, sortSeqbr)
                            end)
     

 
  val three_bodies = Seq.cons body1 (Seq.cons body2 (Seq.cons body3 (Seq.empty())))
  val three_bodies_tree = Cell ((Scalar.fromInt 3, p22), bb4,
                                Cell ((Scalar.fromInt 2, p13), bb0,
                                      Single body3, Empty, Empty, Single body2), 
                                Empty, 
                                Empty, 
                                Single body1)
  val true = bhtreeEq (compute_tree three_bodies bb4, three_bodies_tree)
  

  (* TASK *)
  (* too_far p1 p2 bb t determines if point p1 is "too far" from 
   * a region bb with barycenter p2, given a threshold parameter t,
   * for it to be worth recuring into the region
   *)
  fun too_far (p1 : Plane.point) (p2 : Plane.point) (bb : BB.bbox) (t : Scalar.scalar) : bool =
      let val diameter = BB.diameter(bb)
          val distance = Plane.distance p1 p2
          val diaDdis = Scalar.divide(diameter,distance)
          in
            case Scalar.compare(diaDdis,t) of
                  EQUAL=> true
                  |GREATER => false
                  |LESS => true
          end


  (* TASK *)
  (* Computes the acceleration on b from the tree T using the Barnes-Hut
   * algorithm with threshold t
   *)
  fun bh_acceleration (T : bhtree) (t : Scalar.scalar) (b : body) : Plane.vec =
          let val (mb,pb,vb)=b
          in
            case T of 
              Empty=> Plane.zero
              |Single((m,p,v))=> Mechanics.accOnPoint(pb,(m,p))
              |Cell ((m, c), bb, tl,tr,bl,br) => (case too_far pb c bb t of
                                                        true=> Mechanics.accOnPoint(pb,(m,c))
                                                        |false=> let val atl= bh_acceleration tl t b
                                                                     val atr= bh_acceleration tr t b
                                                                     val abl= bh_acceleration bl t b
                                                                     val abr= bh_acceleration br t b
                                                                   in
                                                                    atl ++ atr ++ abl ++ abr
                                                                  end
                                                        ) 
         end
      
  

  (* TASK
     Given a threshold and a sequence of bodies, compute the acceleration
     on each body using the Barnes-Hut algorithm.
   *)
  fun barnes_hut (threshold : Scalar.scalar) (s : body Seq.seq) : Plane.vec Seq.seq = 
      let val bb = BB.fromPoints(Seq.map(fn (m,p,v) => p) s)
          val bhtree = compute_tree s bb
        in
          Seq.map (fn x => bh_acceleration bhtree threshold x) s
        end


  (* Default value of the threshold, theta = 0.5 *)
  val threshold = (Scalar.fromRatio (1,2))

  val accelerations : body Seq.seq -> Plane.vec Seq.seq = barnes_hut threshold

end
