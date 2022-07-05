(*
 * ISet - Interval sets
 * Copyright (C) 1996-2003 Xavier Leroy, Nicolas Cannasse, Markus Mottl, Jacek Chrzaszcz,
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version,
 * with the special exception on linking described in file LICENSE.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *)

(*
    Autor:     Kacper Kramarz-Fernandez (indeks: 429629, gr. IV)
    Reviewer:  Jakub Rożek (gr. IV)
    Zadanie 3: Drzewa AVL
*)
open Int;;

(** Interval Set.
    This is an interval set, i.e. a set of integers, where large
    intervals can be stored as single elements. Intervals stored in the
    set are disjoint. 
*)
type t = 
  | Empty
    (* Node: subtree, set, subtree, height, number of integers in the tree *)
  | Node of t * (int*int) * t * int * int
;;

let height = function
  | Node (_,_,_,h,_) -> h
  | Empty -> 0
;;

let weight = function
  | Node (_,_,_,_,w) -> w
  | Empty -> 0
;;

(* Plus operator for safe addition of unsigned integers (within bounds of [0, max_int]) *)
let ( +| ) (a : int) (b : int) =
  if a+b<0 then max_int
  else a+b 
;;

(* Checks whether an integer lies in the given interval *)
let btw x (a,b) = (a <= x && x <= b);;

let empty = Empty;;

let is_empty x = x = Empty;;

(* Gets the width of an interval *)
let width (a,b) = 
  if b-a+1<=0 then max_int
  else b-a+1
;;

(* Creates an unbalanced node *)
let make l (a,b) r = 
  Node (l,(a,b),r, 
        1 + (max (height l) (height r)),
        (weight l) +| (weight r) +| (width (a,b)))
;;

(* Balances out a tree *)
let rec bal l v r =
  let hl = height l
  in let hr = height r
  in 
    if hl > hr + 2 then
      match l with
      | Node (ll,lv,lr,_,_) ->
        if height ll>= height lr then make ll lv (bal lr v r)
        else (match lr with
          | Node (lrl, lrv, lrr, _, _) -> make (make ll lv lrl) lrv (bal lrr v r)
          | Empty -> assert false)
      | Empty -> assert false

    else if hr > hl + 2 then
      match r with
      | Node (rl, rv, rr, _, _) -> 
        if height rr >= height rl then make (bal l v rl) rv rr 
        else (match rl with
          | Node (rll, rlv, rlr, _, _) ->
            make (bal l v rll) rlv (make rlr rv rr)
          | Empty -> assert false)
      | Empty -> assert false  

    else make l v r 
;; 

(* Applies `f` on the path of the set leading to a node with value <=`x`*)
let rec fold_path f acc x set = 
  match set with
  | Node (l, (a,b), r, _, _) ->
    if x<a then f (fold_path f acc x l) set 
    else if x>b then f (fold_path f acc x r) set
    else f acc set
  | Empty -> f acc set
;;

(* Returns a pair: minimal element of set, set without said element *)
let remove_min set = 
  let f (min_val,acc) = function
    | Empty -> (min_val,acc)
    | Node (l,v,r,_,_) ->
      if l = Empty then (v,r)
      else (min_val, bal acc v r)
  in fold_path f ((min_int, min_int), Empty) min_int set
;;

(* Returns a pair: maximal element of set, set without said element *)
let remove_max set = 
  let f (max_val,acc) = function
    | Empty -> (max_val,acc)
    | Node (l,v,r,_,_) ->
      if r = Empty then (v,l)
      else (max_val, bal l v acc)
  in fold_path f ((max_int, max_int), Empty) max_int set
;;

(* Merges two trees, balancing them *)
let merge l r =
  match l,r with
  | Empty,_ -> r 
  | _,Empty -> l
  | _ -> 
    let (k,nr) = remove_min r 
    in bal l k nr
;; 

let split x set = 
  let f = fun (l_acc,found,r_acc) set ->
    match set with
    | Empty -> (l_acc,found,r_acc)
    | Node (l,(a,b),r,_,_) ->
      let new_l =
        if a<x then bal l (a, min b (x-1)) l_acc
        else if a=x then merge l l_acc
        else l_acc
      and new_r = 
        if b>x then bal r_acc (max a (x+1), b) r
        else if b=x then merge r r_acc
        else r_acc 
      in 
      if btw x (a,b)
        then (new_l,true,new_r)
      else (new_l,found,new_r)
  in fold_path f (Empty,false,Empty) x set
;;

let mem x set =
  let f acc = function 
    | Node (_,(a,b),_,_,_) ->
      if btw x (a,b) then true
      else acc
    | Empty -> false
  in fold_path f false x set
;;

let add (new_a, new_b) set = 
  let (l,_,rr) = split new_a set
  in let (_,_,r) = split new_b rr
  in let ((new_a,_), l) = 
    if (l != Empty)&&(mem (new_a-1) l) then remove_max l 
    else ((new_a,new_b),l)
  in let ((_,new_b),r) = 
    if (r != Empty)&&(mem (new_b+1) r) then remove_min r 
    else ((new_a,new_b),r)
  in bal l (new_a,new_b) r 
;;

let remove (new_a,new_b) set = 
  let (l,_,rr) = split new_a set
  in let (_,_,r) = split new_b rr
  in merge l r 
;;

let rec iter f = function
  | Node (l,v,r,_,_) -> iter f l; f v; iter f r
  | Empty -> ()
;;

let rec fold f set acc =
  match set with
  | Node (l,v,r,_,_) -> fold f r (f v (fold f l acc))
  | Empty -> acc
;;

let elements set = 
  let rec loop acc = function
    | Node (l,v,r,_,_) -> loop (v::(loop acc r)) l
    | Empty -> acc
  in loop [] set
;;

let below x set = 
  let f acc = function
    | Node (l, (a,b),_,_,_) ->
      if x>=a then acc +| (weight l) +| (width (a, (min x b)))
      else acc
    | Empty -> acc
  in fold_path f 0 x set
;;  
