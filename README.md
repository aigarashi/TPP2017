# The 13th Theorem Proving and Provers Meeting (TPP 2017)

TPP (Theorem Proving and Provers) ミーティングは，2005 年から年に１回開催され，定理証明系を作っている人から使う側の人まで幅広い人たちが集まり，様々な側面からの話をしてアイディアの交換をしてきたものです．

ミーティング期間中の討論を大切にしたいと考えていますので，出来上がった仕事の講演だけでなく，進行中の仕事，未完成の仕事についての講演も歓迎します．参加者には可能な限りご講演いただきたいと希望しています．

## Logistic Information

### 日付 / Date

2017年12月6日(水)午後〜12月7日(木) / From Wednesday, December 6, afternoon to Thursday, December 7, evening.

### 会場 / Venue

会場は初日と二日目で違うので注意してください．The venues are different on the first and second day.

- Dec. 6: 
京都大学 総合研究７号館１階情報２講義室 / Joho 2 Lecture Room, Research Building No. 7（[地図](http://www.kyoto-u.ac.jp/ja/access/campus/yoshida/map6r_y/)の 68 番の建物 / The building No. 68 in this [map](http://www.kyoto-u.ac.jp/ja/access/campus/yoshida/map6r_y/)）
- Dec. 7:  京都大学 工学部総合校舎２階２１３号室 / Room 213, Faculty of Engineering Integrated Research Bldg.（[地図](http://www.kyoto-u.ac.jp/ja/access/campus/yoshida/map6r_y/)の 53 番の建物 / The building No. 53 in this [map](http://www.kyoto-u.ac.jp/ja/access/campus/yoshida/map6r_y/)）

### 住所 / Address

606-8501 京都市左京区吉田本町 / Yoshida-Honmachi, Sakyo-ku, Kyoto 606-8501

### 懇親会 / Dinner party

* 日時: 12/6(水) 18:00〜
* 会場: [百万遍 しゃらく](https://r.gnavi.co.jp/k614100/)

### 幹事 / Organizer

五十嵐 淳(京都大学 情報学研究科) / Atsushi IGARASHI (Graduate School of Informatics, Kyoto University) [問い合わせはこちらへ](mailto:tpp2017@fos.kuis.kyoto-u.ac.jp)

## 参加申込 / Registration

[こちらからお願いします．](https://docs.google.com/forms/d/e/1FAIpQLSeNY78Nptel4SY_U5MAGMX6qEzyipeFBSnGdCxP-oVkzS9jFA/viewform)

## Technical Program

### 12/6(水)

* 13:30〜13:40 (オープニング)

* 13:40〜14:10 田中哲(産業技術総合研究所)「Coq からの低レベル C コード生成」

> 我々は Coq から C コードを生成する Coq plugin を開発している。Coq から C コードを生成することにより、検証された高速なコードを実現でき、また、さまざまなプログラミング言語から生成したコードを利用できる。この講演では、SSE を利用した HTML escape 関数を例として Coq から低レベルな C コードを生成する方法について述べる。我々の方法では、プログラムを Coq 内で記述することにより検証を可能とし、 また SSE のような CPU の機能を直接使うことも可能であり、高速なコードを生成できる。

* 14:10〜15:00 佐藤雅彦(京都大学): A common notation system for both the lambda-calculus and combinatory logic

> We present a notation system which can be used to faithfully represent both the terms of lambda calculus and combinatory logic. We show the faithfulness of the representations by observing that the representations respect the beta and eta reduction rules.

* 15:00〜15:30 (休憩)

* 15:30〜16:00 HUGUNIN, Jasper(東京工業大学) "Inductive-Inductive definitions in intensional type theory"

> Forsbergの卒業論文で，extensional type theoryで Inductive-Inductive typesをindexed inductive typesに変換する方法があった．しかし，それは uniqueness of identity proofsを必須としていたので，直接 intensional type theoryで同じことはできない．この講演で進行中のintensional type theoryでの変換方法を発表します．

* 16:00〜16:30 中野圭介(電気通信大学): ComplCoq: Coq のための Rewrite Hint 完備化プラグイン

### 12/7(木)

* 10:00〜10:30 坂口和彦(筑波大学): Program Extraction for Mutable Arrays

> We present a mutable array programming library for the Coq proof assistant which enables simple reasoning method based on Ssreflect/Mathematical Components, and extractions of the efficient OCaml programs using in-place updates.  To refine the performance of extracted programs, we improved the extraction plugin of Coq. The improvements are based on trivial transformations for purely functional programs and reduce the construction and destruction costs of (co)inductive objects, and function call costs effectively.  As a concrete application for our library and the improved extraction plugin, we provide efficient implementations, proofs, and benchmarks of two algorithms: the union-find data structure and the quicksort algorithm.

* 10:30〜10:50 小林直樹、押川広樹(東京大学): Higher-Orer Program Verification in Coq via Reduction to HFL Model Checking
<!-- 15〜20分で十分 -->
> HFLモデル検査への帰着を利用して、Coqを用いて高階プログラムの検証を行う試みについて紹介する。

* 10:50〜11:30 小島健介(京都大学)他: TPPmark 2017

* 11:30〜13:30 (休憩)

* 13:30〜14:00 師玉康成(信州大学工学部電子情報システム工学科): Mizarによる微分幾何形式化の準備状況(陰関数定理)

> Mizarによる微分幾何の形式化の準備状況を概説する。当面の目標はストークス定理などの形式化であるが、現状、陰関数定理まで形式化ができているのでこれを中心に経過を報告する。

* 14:00〜14:30 岡崎裕之(信州大学): Mizarによる計算量のためのアルゴリズムの形式化について
<!-- 師玉さんの後 -->
> 形式検証技術を用いた暗号システムの安全性評価実現のためには計算量理論についての形式化を行う必要がある。そのために現在（確率的）アルゴリズムを形式記述方法を模索している。本講演ではその途中経過を紹介する。

* 14:30〜15:00 Reynald Affeldt (産業技術総合研究所): (仮)形式的な情報・符号理論のライブラリに向けて

* 15:00〜15:30 (休憩)

* 15:30〜16:00 南出靖彦 (東京工業大学): 正規表現マッチングにおけるPOSIX戦略の定式化の再考

* 16:00〜16:30 水野雅之 (東北大学情報科学研究科): (TBA)

## TPPmark (出題: 小島健介さん)

今回は，最長共通部分列(LCS)に関する問題です．解答は[問い合わせ先](mailto:tpp2017@fos.kuis.kyoto-u.ac.jp)までお送りください．

### 定義

ここでは部分列として，連続するとは限らないものを考えます．一般に長さ n の列の部分列は最大で 2^n 通りあります．例えば ABC の部分列は ε, A, B, C, AB, BC, AC, ABC の8つです（εは空列）．

二つの有限列 s, t の共通部分列とは，s の部分列でも t の部分列でもあるような列のことをいい，最長共通部分列とは共通部分列の中で最も長いものをいいます．最長共通部分列は一意とは限りません．例えば，AB と BA はいずれも ABA と BAB の最長共通部分列です．

### 問題

1. 二つの有限列 `s` と `t` を受け取って，その最長共通部分列（の一つ）を返す関数 `LCS` を定義してください．列はリストなど使用する証明支援系にある適切なデータ構造を使ってください．また，列の要素の型は自然数など適当な型に固定して構いません．
1. 定義した関数が共通部分列を返す，つまり `LCS s t` が `s` と `t` のいずれの部分列にもなっていることを証明してください（必要ならば，部分列であることを表す述語も定義した上で）．
1. 定義した関数が返す共通部分列が最長である，つまり `u` も `s` と `t` の共通部分列ならば `u` の長さは `LCS s t` の長さ以下であることを証明してください．

最長共通部分列を求めるアルゴリズムとしてよく知られているのは動的計画法によるものです（[Wikipedia](https://en.wikipedia.org/wiki/Longest_common_subsequence_problem)にも解説があります）が，ここでは実装の方針は問いません．素朴に全数探索するアルゴリズムも考えられますし，証明が簡潔に書けることを重視しても面白いかもしれません．

## Past TPPs

* [2016](http://pllab.is.ocha.ac.jp/~asai/tpp2016/)
* [2015](https://sites.google.com/a/progsci.info.kanagawa-u.ac.jp/tpp2015/)
* [up to 2014](https://sites.google.com/a/progsci.info.kanagawa-u.ac.jp/tpp2015/home/guo-qunotpp)
