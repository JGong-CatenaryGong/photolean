# theories/BEP/literature/ — local copies of cited sources

This directory holds *local copies* of sources used while building `theories/BEP/LITERATURE.md`
(PDFs and full-text snapshots retrieved during the survey rounds). Per the repository's hygiene
rule the copies themselves are **not committed** (`.gitignore` ignores
`theories/BEP/literature/*` except this README): what is committed is the record — source, locus,
status (`first-hand` / `not-accessed`) and the formalizable implication — in
`theories/BEP/LITERATURE.md`.

Because the copies are not versioned, **no claim in the record may rest on a local copy alone**:
every entry names a checkable locus (journal, volume, pages, DOI, equation/table number) so that a
reader can re-retrieve it. Entries whose body could not be read are marked `not-accessed` and are
used only for naming/attribution, never for content.

本目录存放调研期间抓取的文献副本（PDF / 全文快照）。按仓库卫生规则，**副本本身不入库**
（`.gitignore` 忽略 `theories/BEP/literature/*`，只保留本 README）：入库的是
`theories/BEP/LITERATURE.md` 里的记录 —— 源、位点、状态（`first-hand` / `not-accessed`）与
可形式化含义。因此记录中任何主张都不依赖本地副本，而必须给出可核查的位点（期刊、卷、页、DOI、
公式/表号），以便读者重新取回；正文不可读者标 `not-accessed`，只用于命名/归属，不用于内容主张。
