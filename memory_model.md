# Sabiメモリモデル
Stacked Borrowsライクメモリモデル

## 考えてないこと
- メモリレイアウト
- [参照値](https://www.ralfj.de/blog/2018/07/24/pointers-and-bytes.html)

## 概要
参照(含む生ポインタ)は`(アドレス, タグ)`の二つ組を値として持つ．

各アドレスに付随する**借用スタック**を用いて有効な参照の管理を行う．
借用スタックの要素は参照の**作成**または**使用**に伴って変化する．

借用スタックはスロット(`(借用種別, タグ集合)`の組)のスタックとして表現される．
つまり，
```isabelle
(* Stacked Borrowsからそのまま借りた *)
datatype refkind = Unique | SharedReadOnly | SharedReadWrite
type_synonym tag_stacks = (refkind * tag set) stack list
```
ただし，一番外側のリストは(アロケートされた)アドレスからそのアドレスに付随するタグスタックへの部分関数を表す．
借用種別は次の3種類．
1. Unique. ユニーク参照を表す．`&mut`に対応．このスロットはタグの要素数が1個で無ければならない．
2. SharedReadOnly．読み込みのみ可能な共有参照．概ね`&`に対応．
3. SharedReadWrite．読み書き両用の共有参照．概ね生ポインタに対応．あとは`&UnsafeCell<T>`とか．

### 参照の作成
Rustプログラム内で得られる参照は，アロケート時に得られるルート参照か，他の有効な参照から再借用してできた参照のいずれかである．
このとき，その参照にはフレッシュなタグが割り振られ，そのタグが該当アドレスの借用スタックに追加される．

SharedReadOnlyな参照からUniqueやSharedは再借用できない(書き込み不可なので)．
また，SharedReadWrite/ReadOnlyから同じ種類の参照を再借用するときにはスタックは増えずに単に集合にタグを入れる．
参照の作成による借用スタックの変化関係を定式化すると次の通りか．
```isabelle
inductive reborrow_stack :: "(refkind * tag set) stack => bool" where
    (* アロケーションはUniqueをルートとする *)
    BorrowRoot: "reborrow_stack [(Unique, {t})]" |
    
    (* Uniqueからは全ての参照が再借用できる *)
    ReborrowUniqueUnique: "reborrow_stack ((Unique, {t}) # tail) ==> reborrow_stack ((Unique, {t'}) # (Unique, {t}) # tail)" |
    ReborrowUniqueSRW: "reborrow_stack ((Unique, {t}) # tail) ==> reborrow_stack ((SharedReadWrite, ts) # (Unique, {t}) # tail)" |
    ReborrowUniqueSRO: "reborrow_stack ((Unique, {t}) # tail) ==> reborrow_stack ((SharedReadOnly, ts) # (Unique, {t}) # tail) |
    
    (* SharedReadWriteからも全ての参照が再借用できる *)
    ReborrowSRWUnique: "reborrow_stack ((SharedReadWrite, ts) # tail) ==> reborrow_stack ((Unique, {t}) # (SharedReadWrite, ts) # tail) |
    (* SharedReadWrite -> SharedReadWriteという再借用は同じタグ集合に突っ込む *)
    ReborrowSRWSRW: "reborrow_stack ((SharedReadWrite, ts) # tail) ==> reborrow_stack ((SharedReadWrite, insert t ts) # tail)" |
    ReborrowSRWSRO: "reborrow_stack ((SharedReadWrite, ts) # tail) ==> reborrow_stack ((SharedReadOnly, ts') # (SharedReadWrite, ts) # tail) |

    (* SharedReadOnlyからの再借用はSharedReadOnlyのみ，同じ集合へ *)
    ReborrowSROSRO: "reborrow_stack ((SharedReadOnly, ts) # tail) ==> reborrow_stack ((SharedReadOnly, insert t ts) # tail)
```

ちなみに，SPARKにRust-like borrowingを入れた拡張ではWriteOnlyな参照も取り入れている．
これは未初期化メモリに対する参照を意味する．
一方で，Rustでは未初期化メモリに対する参照は`MaybeUninit<T>`への参照として表現される[^1]．

[^1]: Rustの意味論では妥当(valid)な値の種類など，型に応じて変わる部分がいくつかある．

### 参照の使用
参照の使用は次の2種類がある．それぞれのアクセスによって借用スタックの変更方法が変わる．
1. 読み込みアクセス
2. 書き込みアクセス

再借用は新しく作られる参照の種別に応じてアクセスを行う．
- `&mut *r`, `r as *mut T`は書き込みアクセス
- `&*r`は読み込みアクセス
その後，上の「参照の作成」に従って新しい参照が借用スタックに追加される．

#### 書き込みアクセス
まずは書き込みアクセスから扱う．
アドレス`p`へのタグ`t`つき参照`Reference p t`に対して書き込みアクセスを行った場合，
1. `tag_stacks ! p`をトップから探索し，`t`を含むUniqueまたはSharedReadWriteなスロットを探す．見つからなかったらUB
2. 見つかったスロットより上のスロットをポップする．
という形で借用スタックを変更する．

このアルゴリズムの直観は，見つかったスロットとその上のスロットについて場合分けをすると分かりやすい．
まず，見つかったスロットがUniqueな場合，書き込みアクセスの前にこの参照の唯一性を回復しなければならない．
したがって，その上のスロットはポップされる．
見つかったスロットがSharedReadWriteの場合，その上にはUniqueまたはSharedReadOnlyが載っている．
Uniqueが載っていた場合はSharedReadWriteへの書き込みによってそれの唯一性が失われているので，ポップする．
一方，SharedReadOnlyが載っていた場合も参照先の不変性が失われるので，ポップする．

#### 読み込みアクセス
参照`Reference p t`に対して読み込みアクセスを行った場合の借用スタックの変化を述べる．
1. `tag_stack ! p`をトップから探索し，`t`を含むスロットを探す．見つからなかったらUB
2. 見つかったスロットの上のスロットがSharedReadOnlyでない場合，そこから上をポップする．

これは，`t`を含むスロットの直上に一時的にSharedReadOnlyな参照を追加する，といった振る舞いである．
SharedReadOnlyは必ずスタックトップに来るため，見つかったスロットの上にSharedReadOnly以外が載っている場合はそれを除かなくてはならない．

本当のStacked Borrowsではこれよりやや緩いルールを用いている．そうしないと誤って弾かれてしまうプログラムが出てしまうらしい．
Sabiにおいてもそのようなケースを考えてあげることでもうちょっと深い理解を元にしたルールが作れそう．

TODO: stack protector, disabled unique