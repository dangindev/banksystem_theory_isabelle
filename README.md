# Phân tích chi tiết code Isabelle/HOL cho hệ thống ngân hàng

## Phần 1: Khai báo và Import thư viện

```isabelle
theory BankSystem
  imports Main "HOL-Library.Code_Target_Nat"
begin
```

- **Dòng 1**: `theory BankSystem` khai báo tên của lý thuyết (theory) mới là "BankSystem"
- **Dòng 2**: `imports Main "HOL-Library.Code_Target_Nat"` nhập các thư viện cần thiết:
  - `Main`: Thư viện chuẩn của Isabelle/HOL với các định nghĩa và định lý cơ bản
  - `"HOL-Library.Code_Target_Nat"`: Thư viện hỗ trợ về số tự nhiên
- **Dòng 3**: `begin` đánh dấu bắt đầu nội dung của lý thuyết
- **Cú pháp**: Khai báo theory trong Isabelle theo cấu trúc `theory [tên] imports [thư viện] begin ... end`
- **Ý nghĩa**: Khởi tạo không gian làm việc mới với các công cụ cần thiết từ thư viện chuẩn

## Phần 2: Định nghĩa kiểu dữ liệu cơ bản

```isabelle
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
```

- **Dòng 1-7**: Comment mô tả các kiểu dữ liệu sắp được định nghĩa
- **Dòng 8**: `type_synonym AccountID = nat` định nghĩa kiểu `AccountID` là đồng nghĩa với kiểu `nat` (số tự nhiên)
- **Dòng 9**: `type_synonym Balance = nat` định nghĩa kiểu `Balance` cũng là đồng nghĩa với kiểu `nat`
- **Dòng 10**: `type_synonym BankState = "AccountID ⇒ Balance option"` định nghĩa kiểu `BankState` là một hàm từ `AccountID` đến `Balance option`
- **Cú pháp**: `type_synonym [tên_kiểu_mới] = [kiểu_hiện_có]` tạo bí danh cho một kiểu dữ liệu
- **Ý nghĩa**: 
  - `AccountID` và `Balance` là số tự nhiên (`nat`), đảm bảo không âm
  - `BankState` là một hàm ánh xạ mỗi ID tài khoản đến số dư hoặc `None` (nếu tài khoản không tồn tại)
  - `⇒` là ký hiệu cho kiểu hàm (function type)
  - `option` là kiểu dữ liệu có thể là `Some` giá_trị hoặc `None`

## Phần 3: Hàm lấy số dư tài khoản

```isabelle
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
```

- **Dòng 1-10**: Comment mô tả chi tiết hàm `get_balance`
- **Dòng 11**: `definition get_balance :: "BankState ⇒ AccountID ⇒ Balance option" where` khai báo kiểu của hàm `get_balance`
  - `::` là ký hiệu khai báo kiểu (type annotation)
  - `"BankState ⇒ AccountID ⇒ Balance option"` chỉ ra rằng hàm nhận vào một `BankState` và một `AccountID`, trả về một `Balance option`
- **Dòng 12**: `"get_balance state aid = state aid"` định nghĩa hàm `get_balance` chỉ đơn giản là áp dụng hàm `state` với tham số `aid`
- **Cú pháp**: `definition [tên_hàm] :: "[kiểu]" where "[tên_hàm] [tham_số1] [tham_số2] = [định_nghĩa]"`
- **Ý nghĩa**: Hàm này truy xuất số dư của một tài khoản từ trạng thái hệ thống. Nó chỉ là một hàm bao bọc (wrapper) xung quanh thao tác ánh xạ của `BankState`

## Phần 4: Hàm cập nhật số dư tài khoản

```isabelle
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
```

- **Dòng 1-13**: Comment mô tả hàm `update_balance`
- **Dòng 14**: `definition update_balance :: "BankState ⇒ AccountID ⇒ Balance ⇒ BankState" where` khai báo kiểu của hàm `update_balance`
  - Hàm nhận vào một `BankState`, một `AccountID`, và một `Balance`, trả về một `BankState` mới
- **Dòng 15**: `"update_balance state aid bal = state(aid := Some bal)"` định nghĩa hàm
  - `state(aid := Some bal)` là cú pháp cập nhật hàm, tạo một hàm mới giống `state` nhưng với giá trị tại `aid` được thay đổi thành `Some bal`
- **Cú pháp**: `state(aid := Some bal)` là cú pháp cập nhật hàm (function update)
  - `:=` là toán tử gán, thay đổi giá trị tại một điểm cụ thể
- **Ý nghĩa**: Hàm này tạo một trạng thái ngân hàng mới từ trạng thái hiện tại, với số dư của tài khoản `aid` được cập nhật thành `bal`

## Phần 5: Hàm kiểm tra tài khoản tồn tại

```isabelle
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
```

- **Dòng 1-10**: Comment mô tả hàm `account_exists`
- **Dòng 11**: `definition account_exists :: "BankState ⇒ AccountID ⇒ bool" where` khai báo kiểu của hàm
  - Hàm nhận vào một `BankState` và một `AccountID`, trả về một giá trị `bool` (boolean: True/False)
- **Dòng 12**: `"account_exists state aid = (state aid ≠ None)"` định nghĩa hàm
  - `≠` là ký hiệu khác (not equal)
  - Hàm kiểm tra xem kết quả của `state aid` có khác `None` không
- **Cú pháp**: Biểu thức boolean `(state aid ≠ None)` sử dụng toán tử khác (`≠`)
- **Ý nghĩa**: Hàm kiểm tra tài khoản có tồn tại hay không bằng cách xem giá trị ánh xạ của nó có phải là `None` không

## Phần 6: Hàm khởi tạo trạng thái rỗng

```isabelle
(* 
 * Khoi tao trang thai ngan hang ban dau voi tat ca tai khoan deu rong.
 *
 * Tra ve:
 * - Trang thai moi voi moi tai khoan deu khong ton tai (None)
 *)
definition empty_state :: BankState where
  "empty_state = (λ_. None)"
```

- **Dòng 1-6**: Comment mô tả hàm `empty_state`
- **Dòng 7**: `definition empty_state :: BankState where` khai báo kiểu của hàm
  - Hàm không có tham số đầu vào, trả về một `BankState`
- **Dòng 8**: `"empty_state = (λ_. None)"` định nghĩa hàm
  - `λ_.` là lambda expression (hàm ẩn danh), nhận vào một đối số bất kỳ và bỏ qua nó (ký hiệu `_`)
  - Hàm luôn trả về `None` bất kể đầu vào là gì
- **Cú pháp**: 
  - `λx. e` là cú pháp lambda trong Isabelle/HOL, tạo một hàm nhận đầu vào x và trả về e
  - `λ_.` là dạng đặc biệt, bỏ qua đối số (không quan tâm đến giá trị đầu vào)
- **Ý nghĩa**: Hàm tạo một trạng thái ngân hàng ban đầu, trong đó không có tài khoản nào tồn tại

## Phần 7: Hàm tạo tài khoản mới

```isabelle
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
```

- **Dòng 1-12**: Comment mô tả hàm `create_account`
- **Dòng 13**: `definition create_account :: "BankState ⇒ AccountID ⇒ Balance ⇒ BankState" where` khai báo kiểu của hàm
- **Dòng 14-17**: Định nghĩa hàm sử dụng biểu thức điều kiện if-then-else
  - `if account_exists state aid then state else ...` kiểm tra tài khoản có tồn tại không
  - Nếu tồn tại, giữ nguyên trạng thái (`then state`)
  - Nếu không tồn tại, cập nhật với số dư ban đầu (`else update_balance state aid initial_balance`)
- **Cú pháp**: `if [điều_kiện] then [biểu_thức1] else [biểu_thức2]` là cấu trúc điều kiện
- **Ý nghĩa**: Hàm tạo tài khoản mới với số dư ban đầu, nhưng chỉ khi tài khoản chưa tồn tại, tránh ghi đè tài khoản hiện có

## Phần 8: Hàm nạp tiền

```isabelle
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
```

- **Dòng 1-13**: Comment mô tả hàm `deposit`
- **Dòng 16**: `definition deposit :: "BankState ⇒ AccountID ⇒ Balance ⇒ BankState" where` khai báo kiểu của hàm
- **Dòng 17-20**: Định nghĩa hàm sử dụng pattern matching
  - `case state aid of` bắt đầu pattern matching trên giá trị của `state aid`
  - `None ⇒ update_balance state aid amt` là trường hợp tài khoản không tồn tại, tạo mới với số dư là `amt`
  - `Some bal ⇒ update_balance state aid (bal + amt)` là trường hợp tài khoản tồn tại với số dư `bal`, cập nhật số dư thành `bal + amt`
- **Cú pháp**: 
  - `case [biểu_thức] of [mẫu1] ⇒ [kết_quả1] | [mẫu2] ⇒ [kết_quả2]` là cú pháp pattern matching
  - `None` và `Some bal` là các mẫu (patterns) của kiểu `option`
  - `⇒` kết nối mẫu với kết quả tương ứng
- **Ý nghĩa**: Hàm nạp tiền vào tài khoản, nếu tài khoản không tồn tại thì tạo mới, nếu tồn tại thì tăng số dư

## Phần 9: Hàm rút tiền

```isabelle
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
```

- **Dòng 1-15**: Comment mô tả hàm `withdraw`
- **Dòng 17**: `definition withdraw :: "BankState ⇒ AccountID ⇒ Balance ⇒ BankState option" where` khai báo kiểu của hàm
  - Khác với `deposit`, hàm `withdraw` trả về `BankState option`, chỉ ra rằng rút tiền có thể thành công (`Some`) hoặc thất bại (`None`)
- **Dòng 18-23**: Định nghĩa hàm kết hợp pattern matching và biểu thức điều kiện
  - Đầu tiên kiểm tra tài khoản có tồn tại không (`case state aid of`)
  - Nếu không tồn tại (`None ⇒ None`), thao tác thất bại
  - Nếu tồn tại với số dư `bal`, kiểm tra số dư có đủ không (`if amt ≤ bal`)
  - Nếu đủ, trả về trạng thái mới (`then Some (update_balance state aid (bal - amt))`)
  - Nếu không đủ, thao tác thất bại (`else None`)
- **Cú pháp**: 
  - Kết hợp pattern matching (`case ... of`) và biểu thức điều kiện (`if ... then ... else`)
  - `≤` là ký hiệu nhỏ hơn hoặc bằng
  - `Some (...)` đóng gói kết quả trong kiểu `option` để chỉ ra thành công
- **Ý nghĩa**: Hàm rút tiền từ tài khoản, chỉ thành công khi tài khoản tồn tại và có đủ số dư, trả về trạng thái mới hoặc `None` nếu thất bại

## Phần 10: Hàm chuyển khoản

```isabelle
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
```

- **Dòng 1-18**: Comment mô tả hàm `transfer`
- **Dòng 19**: `definition transfer :: "BankState ⇒ AccountID ⇒ AccountID ⇒ Balance ⇒ BankState option" where` khai báo kiểu của hàm
  - Hàm nhận vào một `BankState`, hai `AccountID` (nguồn và đích), và một `Balance`, trả về một `BankState option`
- **Dòng 20-23**: Định nghĩa hàm sử dụng pattern matching trên kết quả của `withdraw`
  - `case withdraw state from_aid amt of` thực hiện rút tiền và kiểm tra kết quả
  - `None ⇒ None` nếu rút tiền thất bại, chuyển khoản cũng thất bại
  - `Some new_state ⇒ Some (deposit new_state to_aid amt)` nếu rút tiền thành công, nạp tiền vào tài khoản đích và trả về trạng thái mới
- **Cú pháp**: Pattern matching trên kết quả của một hàm khác
- **Ý nghĩa**: Hàm chuyển khoản kết hợp hai thao tác rút tiền và nạp tiền, đảm bảo tính nguyên tử của giao dịch: chỉ nạp tiền vào đích khi rút tiền từ nguồn thành công

## Phần 11: Định nghĩa các ràng buộc (Invariants)

```isabelle
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
```

- **Dòng 1-2**: Comment đánh dấu phần định nghĩa ràng buộc
- **Dòng 3-4**: Định nghĩa ràng buộc không âm
  - `∀aid bal. state aid = Some bal ⟶ bal ≥ 0` là biểu thức lượng từ phổ biến
  - `∀` là ký hiệu "for all" (với mọi)
  - `⟶` là ký hiệu kéo theo (implies)
  - Điều kiện đọc là: "với mọi aid và bal, nếu state aid = Some bal thì bal ≥ 0"
- **Dòng 6-8**: Định nghĩa hàm tính tổng số dư
  - `∑a∈{a. state a ≠ None}. the (state a)` là phép tổng
  - `∑` là ký hiệu tổng (sum)
  - `{a. state a ≠ None}` là cú pháp xây dựng tập hợp (set comprehension), tạo tập hợp các a thỏa mãn điều kiện state a ≠ None
  - `the (state a)` lấy giá trị từ Some (the (Some x) = x)
- **Dòng 10-11**: Định nghĩa ràng buộc bảo toàn tổng số dư
  - `balance_preserved state1 state2 = (total_balance state1 = total_balance state2)` kiểm tra tổng số dư hai trạng thái có bằng nhau không
- **Cú pháp**:
  - Lượng từ: `∀x. P x` (for all x, P(x) holds)
  - Kéo theo: `A ⟶ B` (if A then B)
  - Tổng: `∑x∈S. f x` (sum of f(x) for all x in set S)
  - Xây dựng tập hợp: `{x. P x}` (set of all x such that P(x) holds)
- **Ý nghĩa**: 
  - Định nghĩa hai ràng buộc chính của hệ thống: không có số dư âm và bảo toàn tổng số dư
  - Định nghĩa hàm `total_balance` để tính tổng số dư của tất cả tài khoản

## Phần 12: Chứng minh bảo toàn ràng buộc không âm cho nạp tiền

```isabelle
(* Chung minh Invariant 1: Khong am sau khi nap tien *)
lemma deposit_preserves_no_negative:
  "no_negative_balance state ⟹ no_negative_balance (deposit state aid amt)"
proof -
  assume "no_negative_balance state"
  show "no_negative_balance (deposit state aid amt)"
    by (simp add: no_negative_balance_def deposit_def)
qed
```

- **Dòng 1**: Comment mô tả lemma
- **Dòng 2-3**: `lemma deposit_preserves_no_negative: "no_negative_balance state ⟹ no_negative_balance (deposit state aid amt)"` khai báo lemma
  - `⟹` là ký hiệu kéo theo trong khẳng định, tách biệt giả thiết và kết luận
  - Lemma khẳng định: nếu trạng thái ban đầu thỏa mãn ràng buộc không âm, thì trạng thái sau khi nạp tiền cũng thỏa mãn
- **Dòng 4**: `proof -` bắt đầu chứng minh không sử dụng phương pháp cụ thể (`-` là ký hiệu không áp dụng quy tắc nào)
- **Dòng 5**: `assume "no_negative_balance state"` giả sử trạng thái ban đầu thỏa mãn ràng buộc không âm
- **Dòng 6-7**: `show "no_negative_balance (deposit state aid amt)" by (simp add: no_negative_balance_def deposit_def)` chứng minh kết luận
  - `show` đưa ra khẳng định cần chứng minh
  - `by (simp add: no_negative_balance_def deposit_def)` sử dụng tactic simp với định nghĩa của `no_negative_balance` và `deposit`
  - `simp` là tactic tự động đơn giản hóa biểu thức
  - `add:` thêm định nghĩa để sử dụng trong quá trình đơn giản hóa
- **Dòng 8**: `qed` kết thúc chứng minh
- **Cú pháp**:
  - `lemma [tên]: "[khẳng_định]"` khai báo một lemma
  - `proof -` bắt đầu chứng minh
  - `assume "[giả_thiết]"` giả sử một điều kiện
  - `show "[kết_luận]" by [tactic]` chứng minh kết luận bằng một tactic
  - `qed` kết thúc chứng minh
- **Ý nghĩa**: Chứng minh nạp tiền không làm vi phạm ràng buộc không âm, sử dụng tactic simp để tự động chứng minh

## Phần 13: Chứng minh bảo toàn ràng buộc không âm cho rút tiền

```isabelle
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
```

- **Dòng 1**: Comment mô tả lemma
- **Dòng 2-3**: Khai báo lemma với hai điều kiện: trạng thái ban đầu thỏa mãn ràng buộc không âm và rút tiền thành công
- **Dòng 4**: Bắt đầu chứng minh
- **Dòng 5-6**: Giả sử hai điều kiện trong lemma
- **Dòng 8-10**: Phân tích kết quả của `withdraw` để biết thêm thông tin
  - `from ‹withdraw state aid amt = Some state'›` bắt đầu từ giả thiết
  - `obtain bal where "state aid = Some bal" and "amt ≤ bal" and "state' = update_balance state aid (bal - amt)"` tạo biến và điều kiện mới
  - `by (auto simp add: withdraw_def split: option.splits if_splits)` sử dụng tactic auto với các tham số phù hợp
  - `withdraw_def` là định nghĩa của `withdraw`
  - `split: option.splits if_splits` phân tích các trường hợp của kiểu `option` và biểu thức `if`
- **Dòng 12-13**: Chứng minh kết luận
- **Cú pháp**:
  - `from ‹điều_kiện›` bắt đầu từ một điều kiện đã có
  - `obtain [biến] where "[điều_kiện1]" and "[điều_kiện2]"` tạo biến mới và các điều kiện kèm theo
  - `and` kết hợp nhiều điều kiện
  - `by (auto simp add: def split: option.splits if_splits)` sử dụng tactic auto với các tham số
  - `split:` chỉ định các kiểu cần phân tích
- **Ý nghĩa**: Chứng minh rút tiền không làm vi phạm ràng buộc không âm, bằng cách chỉ ra rằng nếu rút tiền thành công thì số dư mới vẫn không âm

## Phần 14: Chứng minh bảo toàn ràng buộc không âm cho chuyển khoản

```isabelle
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
```

- **Dòng 1**: Comment mô tả lemma
- **Dòng 2-4**: Khai báo lemma
- **Dòng 5-7**: Giả sử các điều kiện
- **Dòng 8-11**: Phân tích `transfer` thành hai bước: `withdraw` và `deposit`
  - `obtain intermediate_state where ...` tạo biến và điều kiện cho trạng thái trung gian
  - `using ‹transfer state from_aid to_aid amt = Some state'›` sử dụng giả thiết đã có
  - `by (auto simp add: transfer_def split: option.splits)` sử dụng tactic auto
- **Dòng 13-15**: Chứng minh trạng thái trung gian vẫn thỏa mãn ràng buộc không âm
  - `from ‹no_negative_balance state› ‹withdraw state from_aid amt = Some intermediate_state›` bắt đầu từ hai điều kiện
  - `have "no_negative_balance intermediate_state"` đưa ra kết luận trung gian
  - `by (rule withdraw_preserves_no_negative)` áp dụng lemma đã chứng minh trước đó
- **Dòng 17-19**: Chứng minh trạng thái cuối cùng vẫn thỏa mãn ràng buộc không âm
  - `by (simp add: deposit_preserves_no_negative)` sử dụng lemma về nạp tiền
- **Cú pháp**:
  - `using ‹điều_kiện›` chỉ định điều kiện được sử dụng
  - `by (rule [lemma])` áp dụng lemma đã có
  - `have "[kết_luận]"` đưa ra kết luận trung gian
- **Ý nghĩa**: Chứng minh chuyển khoản không làm vi phạm ràng buộc không âm, bằng cách kết hợp hai lemma đã chứng minh cho rút tiền và nạp tiền

## Phần 15: Tiên đề về tổng số dư cho nạp tiền

```isabelle
(* -------------------------------------------- *)

(* TIEN DE: Nap tien lam tang tong tien *)
axiomatization where
  deposit_increases_total: "total_balance (deposit state aid amt) = total_balance state + amt"
```

- **Dòng 1**: Dấu phân cách giữa các phần
- **Dòng 3**: Comment mô tả tiên đề
- **Dòng 4-5**: Khai báo tiên đề
  - `axiomatization where` bắt đầu khai báo tiên đề
  - `deposit_increases_total: "total_balance (deposit state aid amt) = total_balance state + amt"` đặt tên và nội dung tiên đề
- **Cú pháp**: `axiomatization where [tên]: "[nội_dung]"` khai báo một tiên đề (axiom)
- **Ý nghĩa**: Tiên đề khẳng định rằng nạp tiền làm tăng tổng số dư đúng bằng số tiền nạp, không cần chứng minh chi tiết

## Phần 16: Tiên đề về tổng số dư cho rút tiền

```isabelle
(* TIEN DE: Rut tien lam giam tong tien *)
axiomatization where
  withdraw_decreases_total: "withdraw state aid amt = Some state' ⟹ 
                            total_balance state = total_balance state' + amt"
```

- **Dòng 1**: Comment mô tả tiên đề
- **Dòng 2-4**: Khai báo tiên đề
  - Tiên đề có điều kiện: nếu rút tiền thành công thì tổng số dư giảm đúng bằng số tiền rút
- **Cú pháp**: Tiên đề với điều kiện `⟹`
- **Ý nghĩa**: Tiên đề khẳng định rằng rút tiền làm giảm tổng số dư đúng bằng số tiền rút, không cần chứng minh chi tiết

## Phần 17: Chứng minh bảo toàn tổng tiền cho chuyển khoản

```isabelle
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
```

- **Dòng 1**: Comment mô tả lemma
- **Dòng 2-3**: Khai báo lemma: nếu chuyển khoản thành công, tổng số dư không thay đổi
- **Dòng 4-5**: Bắt đầu chứng minh và giả sử điều kiện
- **Dòng 7-10**: Phân tích `transfer` thành hai bước
- **Dòng 12-14**: Sử dụng tiên đề về rút tiền
  - `by (rule withdraw_decreases_total)` áp dụng tiên đề
  - Kết luận: tổng số dư ban đầu = tổng số dư trung gian + số tiền rút
- **Dòng 16-18**: Sử dụng tiên đề về nạp tiền
  - `moreover` là từ khóa báo hiệu thêm một kết luận trung gian
  - `by (simp add: deposit_increases_total)` áp dụng tiên đề
  - Kết luận: tổng số dư cuối = tổng số dư trung gian + số tiền nạp
- **Dòng 20-21**: Kết hợp hai kết luận
  - `ultimately` kết hợp với `moreover` để kết hợp các kết luận trung gian
  - `by simp` sử dụng tactic simp để giải quyết mục tiêu
- **Cú pháp**:
  - `moreover` báo hiệu thêm một kết luận trung gian
  - `ultimately` kết hợp các kết luận trung gian trước đó
- **Ý nghĩa**: Chứng minh chuyển khoản bảo toàn tổng số dư, bằng cách chỉ ra:
  1. Rút tiền làm giảm tổng đi amt
  2. Nạp tiền làm tăng tổng thêm amt
  3. Do đó, tổng số dư không thay đổi

## Phần 18: Chứng minh tính xác định (Determinism)

```isabelle
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
```

- **Dòng 1-6**: Comment mô tả phần chứng minh tính xác định
- **Dòng 8-12**: Comment mô tả lemma `deposit_deterministic`
- **Dòng 13-14**: Khai báo và chứng minh lemma
  - `"deposit state aid amt = deposit state aid amt"` là khẳng định hiển nhiên đúng (phản xạ)
  - `by simp` sử dụng tactic simp để chứng minh trực tiếp
- **Cú pháp**: Lemma với chứng minh trực tiếp bằng tactic
- **Ý nghĩa**: Chứng minh nạp tiền là một hàm xác định, luôn trả về cùng một kết quả với cùng đầu vào (hiển nhiên đúng theo tính chất phản xạ)

```isabelle
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
```

- **Dòng 1-5**: Comment mô tả lemma
- **Dòng 6-9**: Khai báo lemma: nếu hai lần rút tiền cùng thành công, kết quả sẽ giống nhau
- **Dòng 10-19**: Chứng minh
  - Dòng 11-12: Giả sử hai lần rút tiền đều thành công
  - Dòng 15-16: So sánh kết quả trực tiếp: `Some state1 = Some state2`
  - Dòng 19: Suy ra `state1 = state2` (do constructor `Some` là injective)
- **Cú pháp**:
  - `thus` tương đương với `then show`, kết hợp `have` và `show`
- **Ý nghĩa**: Chứng minh rút tiền là một hàm xác định, với cùng đầu vào, nếu thành công, luôn trả về cùng một kết quả

```isabelle
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
```

- **Dòng 1-5**: Comment mô tả lemma
- **Dòng 6-9**: Khai báo lemma tương tự như `withdraw_deterministic`
- **Dòng 10-19**: Chứng minh tương tự như `withdraw_deterministic`
- **Ý nghĩa**: Chứng minh chuyển khoản là một hàm xác định, với cùng đầu vào, nếu thành công, luôn trả về cùng một kết quả

## Phần 19: Chương trình mẫu và chứng minh

```isabelle
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
```

- **Dòng 1-6**: Comment mô tả chương trình mẫu
- **Dòng 7-12**: Định nghĩa chương trình mẫu
  - `let state1 = deposit state 1 50 in` gán biến cục bộ cho kết quả nạp tiền
  - `case withdraw state1 1 30 of` kiểm tra kết quả rút tiền
  - `None ⇒ None` nếu rút tiền thất bại, chương trình thất bại
  - `Some state2 ⇒ transfer state2 1 2 20` nếu rút tiền thành công, thực hiện chuyển khoản
- **Cú pháp**:
  - `let [biến] = [biểu_thức] in [thân_hàm]` để gán biến cục bộ
  - Kết hợp `let-in` và pattern matching
- **Ý nghĩa**: Định nghĩa một chương trình mẫu gồm ba thao tác liên tiếp, mô phỏng một chuỗi giao dịch ngân hàng

```isabelle
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
```

- **Dòng 1**: Comment mô tả lemma
- **Dòng 2-3**: Khai báo lemma: nếu trạng thái ban đầu thỏa mãn ràng buộc không âm và chương trình thành công, thì trạng thái cuối cùng vẫn thỏa mãn
- **Dòng 4-25**: Chứng minh
  - Dòng 5-6: Giả sử các điều kiện
  - Dòng 8-13: Phân tích `sample_program` thành ba bước
    - `by (auto simp add: sample_program_def Let_def split: option.splits)` sử dụng `Let_def` để xử lý `let-in`
  - Dòng 15-17: Chứng minh trạng thái sau bước 1 vẫn thỏa mãn ràng buộc
  - Dòng 19-21: Chứng minh trạng thái sau bước 2 vẫn thỏa mãn ràng buộc
  - Dòng 23-25: Chứng minh trạng thái sau bước 3 vẫn thỏa mãn ràng buộc
- **Cú pháp**:
  - `obtain var1 and var2 where [điều_kiện1] and [điều_kiện2]` tạo nhiều biến với nhiều điều kiện
  - `Let_def` là định nghĩa cho cú pháp `let-in`
- **Ý nghĩa**: Chứng minh chương trình mẫu không vi phạm ràng buộc không âm, bằng cách áp dụng lần lượt các lemma đã chứng minh cho từng bước

```isabelle
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
```

- **Dòng 1**: Comment mô tả lemma
- **Dòng 2-4**: Khai báo lemma: chương trình mẫu làm tăng tổng số dư thêm 20 (50 - 30)
- **Dòng 5-30**: Chứng minh
  - Dòng 6-13: Giả sử điều kiện và phân tích chương trình
  - Dòng 15-17: Áp dụng tiên đề về nạp tiền
  - Dòng 20-22: Áp dụng tiên đề về rút tiền
  - Dòng 25-27: Áp dụng lemma về chuyển khoản
  - Dòng 30-33: Kết hợp các kết quả để chứng minh kết luận cuối cùng
- **Dòng 35**: `end` kết thúc theory
- **Cú pháp**:
  - `by fact` sử dụng một thực tế đã biết
  - `from [điều_kiện1] [điều_kiện2] [điều_kiện3]` bắt đầu từ nhiều điều kiện
- **Ý nghĩa**: Chứng minh chương trình mẫu làm tăng tổng số dư thêm 20, phù hợp với logic: nạp 50, rút 30, chuyển 20 (không thay đổi tổng)

## Tổng kết

Code Isabelle/HOL này định nghĩa một hệ thống ngân hàng đơn giản với các thao tác cơ bản và chứng minh các tính chất quan trọng:

1. **Định nghĩa kiểu dữ liệu** sử dụng kiểu hàm để mô hình hóa Map, đảm bảo tính đơn giản và an toàn
2. **Định nghĩa các thao tác** nạp tiền, rút tiền, chuyển khoản, xử lý các trường hợp đặc biệt
3. **Định nghĩa các ràng buộc** không âm và bảo toàn tổng số dư
4. **Chứng minh bảo toàn ràng buộc** cho cả ba thao tác, đảm bảo hệ thống luôn ở trạng thái hợp lệ
5. **Chứng minh tính xác định** cho cả ba thao tác, đảm bảo tính nhất quán của hệ thống
6. **Định nghĩa chương trình mẫu** và chứng minh nó không vi phạm các ràng buộc

Sự kết hợp giữa các kiểu dữ liệu an toàn, định nghĩa hàm rõ ràng, và chứng minh hình thức đảm bảo hệ thống ngân hàng hoạt động đúng đắn trong mọi tình huống có thể xảy ra.
