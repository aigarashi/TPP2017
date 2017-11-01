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

6日夜に予定しています． 詳細については少々お待ちください． / Planned on the 6th evening.  Details to be announced.

### 幹事 / Organizer

五十嵐 淳(京都大学 情報学研究科) / Atsushi IGARASHI (Graduate School of Informatics, Kyoto University) [問い合わせはこちらへ](mailto:tpp2017@fos.kuis.kyoto-u.ac.jp)

## 参加申込 / Registration

[こちらからお願いします．](https://docs.google.com/forms/d/e/1FAIpQLSeNY78Nptel4SY_U5MAGMX6qEzyipeFBSnGdCxP-oVkzS9jFA/viewform)

## Technical Program

TBA

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
