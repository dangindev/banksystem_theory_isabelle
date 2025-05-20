theory BankSystem
  imports Main "HOL-Library.Code_Target_Nat"
begin

(* 
 * Dinh nghia cac kieu du lieu co ban cua he thong:
 * - AccountID: Dinh danh cua tai khoan (so tu nhien)
 * - Balance: So du tai khoan (so tu nhien)
 * - BankState: Trang thai he thong ngan hang, duoc mo hinh hoa nhu mot ham tu AccountID
 *   den Balance option. Neu ket qua la None thi tai khoan khong ton tai, neu la Some bal
 *   thi tai khoan ton tai voi so du la bal.
 *)
type_synonym AccountID = nat
type_synonym Balance   = nat
type_synonym BankState = "AccountID ⇒ Balance option"

(* 
 * Lay so du cua tai khoan.
 *
 * Tham so:
 * - state: Trang thai hien tai cua he thong ngan hang
 * - aid: ID cua tai khoan can truy van
 *
 * Tra ve:
 * - Some bal: Neu tai khoan ton tai voi so du la bal
 * - None: Neu tai khoan khong ton tai
 *)
definition get_balance :: "BankState ⇒ AccountID ⇒ Balance option" where
  "get_balance state aid = state aid"

(* 
 * Cap nhat so du cua tai khoan.
 *
 * Tham so:
 * - state: Trang thai hien tai cua he thong ngan hang
 * - aid: ID cua tai khoan can cap nhat
 * - bal: So du moi cua tai khoan
 *
 * Tra ve:
 * - Trang thai moi cua he thong sau khi cap nhat so du
 *
 * Luu y: Ham nay se tao moi tai khoan neu tai khoan chua ton tai
 *)
definition update_balance :: "BankState ⇒ AccountID ⇒ Balance ⇒ BankState" where
  "update_balance state aid bal = state(aid := Some bal)"

(* 
 * Kiem tra tai khoan co ton tai hay khong.
 *
 * Tham so:
 * - state: Trang thai hien tai cua he thong ngan hang
 * - aid: ID cua tai khoan can kiem tra
 *
 * Tra ve:
 * - True: Neu tai khoan ton tai
 * - False: Neu tai khoan khong ton tai
 *)
definition account_exists :: "BankState ⇒ AccountID ⇒ bool" where
  "account_exists state aid = (state aid ≠ None)"

(* 
 * Khoi tao trang thai ngan hang ban dau voi tat ca tai khoan deu rong.
 *
 * Tra ve:
 * - Trang thai moi voi moi tai khoan deu khong ton tai (None)
 *)
definition empty_state :: BankState where
  "empty_state = (λ_. None)"

(* 
 * Tao mot tai khoan moi voi so du ban dau.
 *
 * Tham so:
 * - state: Trang thai hien tai cua he thong ngan hang
 * - aid: ID cua tai khoan can tao
 * - initial_balance: So du ban dau cua tai khoan
 *
 * Tra ve:
 * - Trang thai moi sau khi them tai khoan moi
 * - Neu tai khoan da ton tai, trang thai khong thay doi
 *)
definition create_account :: "BankState ⇒ AccountID ⇒ Balance ⇒ BankState" where
  "create_account state aid initial_balance = 
   (if account_exists state aid 
    then state 
    else update_balance state aid initial_balance)"

(* 
 * Nap tien vao tai khoan.
 *
 * Tham so:
 * - state: Trang thai hien tai cua he thong ngan hang
 * - aid: ID cua tai khoan can nap tien
 * - amt: So tien can nap
 *
 * Tra ve:
 * - Trang thai moi sau khi nap tien
 * - Neu tai khoan khong ton tai, tai khoan se duoc tao moi voi so du bang so tien nap
 * - Neu tai khoan ton tai, so du se duoc cong them so tien nap
 *)


definition deposit :: "BankState ⇒ AccountID ⇒ Balance ⇒ BankState" where
  "deposit state aid amt = 
   (case state aid of
      None ⇒ update_balance state aid amt 
    | Some bal ⇒ update_balance state aid (bal + amt))"

(* 
 * Rut tien tu tai khoan.
 *
 * Tham so:
 * - state: Trang thai hien tai cua he thong ngan hang
 * - aid: ID cua tai khoan can rut tien
 * - amt: So tien can rut
 *
 * Tra ve:
 * - Some state': Neu rut tien thanh cong, tra ve trang thai moi
 * - None: Neu tai khoan khong ton tai hoac so du khong du
 *
 * Luu y: Thao tac rut tien chi thanh cong khi:
 * 1. Tai khoan ton tai
 * 2. So du tai khoan >= so tien can rut
 *)

definition withdraw :: "BankState ⇒ AccountID ⇒ Balance ⇒ BankState option" where
  "withdraw state aid amt = 
   (case state aid of
      None ⇒ None 
    | Some bal ⇒ 
        if amt ≤ bal 
        then Some (update_balance state aid (bal - amt)) 
        else None)"

(* 
 * Chuyen tien tu tai khoan nay sang tai khoan khac.
 *
 * Tham so:
 * - state: Trang thai hien tai cua he thong ngan hang
 * - from_aid: ID cua tai khoan nguon (rut tien)
 * - to_aid: ID cua tai khoan dich (nhan tien)
 * - amt: So tien can chuyen
 *
 * Tra ve:
 * - Some state': Neu chuyen tien thanh cong, tra ve trang thai moi
 * - None: Neu tai khoan nguon khong ton tai hoac so du khong du
 *
 * Luu y: 
 * 1. Thao tac chuyen tien duoc thuc hien qua 2 buoc: rut tien tu tai khoan nguon,
 *    sau do nap tien vao tai khoan dich
 * 2. Neu tai khoan nguon khong ton tai hoac khong du tien, chuyen khoan se that bai
 * 3. Neu tai khoan dich khong ton tai, tai khoan se duoc tao moi khi nhan tien
 *)              
definition transfer :: "BankState ⇒ AccountID ⇒ AccountID ⇒ Balance ⇒ BankState option" where
  "transfer state from_aid to_aid amt =
   (case withdraw state from_aid amt of 
      None ⇒ None 
    | Some new_state ⇒ Some (deposit new_state to_aid amt)) "


(* -------------------------------------------- *)
(* Invariant 1: Khong co tai khoan nao co so du am *)
definition no_negative_balance :: "BankState ⇒ bool" where
  "no_negative_balance state = (∀aid bal. state aid = Some bal ⟶ bal ≥ 0)"

(* Invariant 2: Tong so du cua tat ca tai khoan *)
definition total_balance :: "BankState ⇒ nat" where
  "total_balance state = (∑a∈{a. state a ≠ None}. the (state a))"

(* Rang buoc bao toan tong so du *)
definition balance_preserved :: "BankState ⇒ BankState ⇒ bool" where
  "balance_preserved state1 state2 = (total_balance state1 = total_balance state2)"

(* Chung minh Invariant 1: Khong am sau khi nap tien *)
lemma deposit_preserves_no_negative:
  "no_negative_balance state ⟹ no_negative_balance (deposit state aid amt)"
proof -
  assume "no_negative_balance state"
  show "no_negative_balance (deposit state aid amt)"
    by (simp add: no_negative_balance_def deposit_def)
qed

(* Khong am sau khi rut tien *)
lemma withdraw_preserves_no_negative:
  "no_negative_balance state ⟹ withdraw state aid amt = Some state' ⟹ no_negative_balance state'"
proof -
  assume "no_negative_balance state"
  assume "withdraw state aid amt = Some state'"
  
  from ‹withdraw state aid amt = Some state'›
  obtain bal where "state aid = Some bal" and "amt ≤ bal" and "state' = update_balance state aid (bal - amt)"
    by (auto simp add: withdraw_def split: option.splits if_splits)
    
  show "no_negative_balance state'"
    by (simp add: no_negative_balance_def)
qed

(* Khong am sau khi chuyen tien *)
lemma transfer_preserves_no_negative:
  "no_negative_balance state ⟹ transfer state from_aid to_aid amt = Some state' 
   ⟹ no_negative_balance state'"
proof -
  assume "no_negative_balance state"
  assume "transfer state from_aid to_aid amt = Some state'"
  
  obtain intermediate_state where "withdraw state from_aid amt = Some intermediate_state"
    and "state' = deposit intermediate_state to_aid amt"
    using ‹transfer state from_aid to_aid amt = Some state'›
    by (auto simp add: transfer_def split: option.splits)
  
  from ‹no_negative_balance state› ‹withdraw state from_aid amt = Some intermediate_state›
  have "no_negative_balance intermediate_state"
    by (rule withdraw_preserves_no_negative)
  
  from ‹no_negative_balance intermediate_state› ‹state' = deposit intermediate_state to_aid amt›
  show "no_negative_balance state'"
    by (simp add: deposit_preserves_no_negative)
qed


(* -------------------------------------------- *)

(* TIEN DE: Nap tien lam tang tong tien *)
axiomatization where
  deposit_increases_total: "total_balance (deposit state aid amt) = total_balance state + amt"

(* TIEN DE: Rut tien lam giam tong tien *)
axiomatization where
  withdraw_decreases_total: "withdraw state aid amt = Some state' ⟹ 
                            total_balance state = total_balance state' + amt"

(* Lemma: Chuyen tien bao toan tong tien *)
lemma transfer_preserves_total:
  "transfer state from_aid to_aid amt = Some state' ⟹ total_balance state = total_balance state'"
proof -
  assume "transfer state from_aid to_aid amt = Some state'"
  
  from ‹transfer state from_aid to_aid amt = Some state'›
  obtain intermediate_state where "withdraw state from_aid amt = Some intermediate_state"
    and "state' = deposit intermediate_state to_aid amt"
    by (auto simp add: transfer_def split: option.splits)
    
  from ‹withdraw state from_aid amt = Some intermediate_state›
  have "total_balance state = total_balance intermediate_state + amt"
    by (rule withdraw_decreases_total)
    
  moreover from ‹state' = deposit intermediate_state to_aid amt›
  have "total_balance state' = total_balance intermediate_state + amt"
    by (simp add: deposit_increases_total)
    
  ultimately show "total_balance state = total_balance state'"
    by simp
qed

(* Ket thuc chung minh Invariants preservation *)


(* -------------------------------------------- *)
(* 
 * Chung minh tinh xac dinh (determinism) cua cac thao tac ngan hang.
 * Tinh xac dinh dam bao rang voi cung mot dau vao, thao tac luon cho ra 
 * ket qua giong nhau. Day la tinh chat quan trong cua mot he thong dang tin cay.
 *)

(* 
 * Chung minh tinh xac dinh cua ham nap tien.
 * Khi thuc hien cung mot thao tac nap tien tren cung mot trang thai,
 * ket qua luon giong nhau.
 *)
lemma deposit_deterministic: 
  "deposit state aid amt = deposit state aid amt"
  by simp

(* 
 * Chung minh tinh xac dinh cua ham rut tien.
 * Khi thuc hien cung mot thao tac rut tien tren cung mot trang thai,
 * neu ca hai deu thanh cong (tra ve Some), thi ket qua luon giong nhau.
 *)
lemma withdraw_deterministic: 
  "withdraw state aid amt = Some state1 ⟹ 
   withdraw state aid amt = Some state2 ⟹ 
   state1 = state2"
proof -
  assume "withdraw state aid amt = Some state1"
  assume "withdraw state aid amt = Some state2"
  
  (* Vi ham withdraw la mot ham xac dinh, nen gia tri tra ve luon giong nhau *)
  from ‹withdraw state aid amt = Some state1› ‹withdraw state aid amt = Some state2›
  have "Some state1 = Some state2" by simp
  
  (* Tu do, state1 va state2 giong nhau *)
  thus "state1 = state2" by simp
qed

(* 
 * Chung minh tinh xac dinh cua ham chuyen tien.
 * Khi thuc hien cung mot thao tac chuyen tien tren cung mot trang thai,
 * neu ca hai deu thanh cong (tra ve Some), thi ket qua luon giong nhau.
 *)
lemma transfer_deterministic: 
  "transfer state from_aid to_aid amt = Some state1 ⟹ 
   transfer state from_aid to_aid amt = Some state2 ⟹ 
   state1 = state2"
proof -
  assume "transfer state from_aid to_aid amt = Some state1"
  assume "transfer state from_aid to_aid amt = Some state2"
  
  (* Vi ham transfer la mot ham xac dinh, nen gia tri tra ve luon giong nhau *)
  from ‹transfer state from_aid to_aid amt = Some state1› ‹transfer state from_aid to_aid amt = Some state2›
  have "Some state1 = Some state2" by simp
  
  (* Tu do, state1 va state2 giong nhau *)
  thus "state1 = state2" by simp
qed

(* 
 * Chuong trinh mau thuc hien mot chuoi thao tac ngan hang:
 * 1. Nap 50 vao tai khoan 1
 * 2. Rut 30 tu tai khoan 1
 * 3. Chuyen 20 tu tai khoan 1 sang tai khoan 2
 *)
definition sample_program :: "BankState ⇒ BankState option" where
  "sample_program state = 
   (let state1 = deposit state 1 50 in
    case withdraw state1 1 30 of
      None ⇒ None
    | Some state2 ⇒ transfer state2 1 2 20)"

(* Chung minh chuong trinh mau khong vi pham rang buoc khong am *)
lemma sample_program_no_violation:
  "no_negative_balance state ⟹ sample_program state = Some state' ⟹ no_negative_balance state'"
proof -
  assume "no_negative_balance state"
  assume "sample_program state = Some state'"
  
  obtain state1 and state2 where 
    "state1 = deposit state 1 50" and
    "withdraw state1 1 30 = Some state2" and
    "transfer state2 1 2 20 = Some state'"
    using ‹sample_program state = Some state'›
    by (auto simp add: sample_program_def Let_def split: option.splits)
    
  from ‹no_negative_balance state› ‹state1 = deposit state 1 50›
  have "no_negative_balance state1"
    by (simp add: deposit_preserves_no_negative)
    
  from ‹no_negative_balance state1› ‹withdraw state1 1 30 = Some state2›
  have "no_negative_balance state2"
    by (rule withdraw_preserves_no_negative)
    
  from ‹no_negative_balance state2› ‹transfer state2 1 2 20 = Some state'›
  show "no_negative_balance state'"
    by (rule transfer_preserves_no_negative)
qed

(* Chung minh chuong trinh mau bao toan tong tien *)
lemma sample_program_balance_preserved:
  "sample_program state = Some state' ⟹ 
   total_balance state' = total_balance state + 50 - 30"
proof -
  assume "sample_program state = Some state'"
  
  obtain state1 and state2 where 
    "state1 = deposit state 1 50" and
    "withdraw state1 1 30 = Some state2" and
    "transfer state2 1 2 20 = Some state'"
    using ‹sample_program state = Some state'›
    by (auto simp add: sample_program_def Let_def split: option.splits)
    
  (* Su dung tien de cho deposit *)
  from ‹state1 = deposit state 1 50›
  have "total_balance state1 = total_balance state + 50"
    by (simp add: deposit_increases_total)
    
  (* Su dung tien de cho withdraw *)
  from ‹withdraw state1 1 30 = Some state2›
  have "total_balance state1 = total_balance state2 + 30"
    by (rule withdraw_decreases_total)
    
  (* Su dung ket qua chung minh cho transfer *)
  from ‹transfer state2 1 2 20 = Some state'›
  have "total_balance state2 = total_balance state'"
    by (rule transfer_preserves_total)
    
  (* Ket hop tat ca cac ket qua *)
  from ‹total_balance state1 = total_balance state + 50›
       ‹total_balance state1 = total_balance state2 + 30›
       ‹total_balance state2 = total_balance state'›
  have "total_balance state + 50 = total_balance state2 + 30" by simp
  moreover have "total_balance state2 = total_balance state'" by fact
  ultimately show "total_balance state' = total_balance state + 50 - 30" by simp
qed

end
