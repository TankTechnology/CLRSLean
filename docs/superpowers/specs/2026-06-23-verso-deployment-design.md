# CLRSLean Verso 部署设计

日期: 2026-06-23
状态: 已批准
参考: https://github.com/teorth/analysis

## 目标

将 CLRSLean 的网站从手写静态 HTML 迁移到 Verso 文学编程引擎，
实现与 `teorth/analysis` 同等的书本式阅读体验。

## 架构

```
.lean 源文件 (含 /-! 文学注释)
  → lakefile.lean (启用 doc.verso, 依赖 verso 包)
    → literate.toml (模块排序、章节标题)
      → lake build (编译 Lean)
        → lake build :literateHtml (Verso 生成 HTML)
          → _site/ (完整网站)
            → GitHub Actions → GitHub Pages
```

## 文件结构

```
CLRSLean/
├── CLAUDE.md                  ← Agent 写作指南
├── CLRSLean.lean              ← 顶层入口 + Verso 着陆页
├── CLRSLean/
│   ├── Chapter_02/
│   │   └── Section_02_1_Insertion_Sort.lean
│   ├── Chapter_16/
│   │   └── Section_16_3_Huffman_Codes.lean
│   └── Chapter_23/
│       ├── Section_23_1_Growing_Minimum_Spanning_Trees.lean
│       └── Section_23_2_Kruskal_And_Prim.lean
├── lakefile.lean              ← 从 .toml 改为 .lean DSL
├── literate.toml              ← Verso 配置
├── lean-toolchain             ← 不变 (v4.29.1)
├── docs/proof-map.md          ← 人工维护的状态账本
└── .github/workflows/
    ├── lean_action_ci.yml     ← CI 不变
    └── pages.yml              ← 加 literate 构建步骤
```

## lakefile.lean

```lean
import Lake
open Lake DSL

package «clrs-lean» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`doc.verso, true⟩
  ]
  moreLeanArgs := #[
    "-Dwarn.sorry=false"
  ]

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"

require verso from git
  "https://github.com/leanprover/verso" @ "main"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.1"

@[default_target]
lean_lib «CLRSLean» where
```

## literate.toml

```toml
landing_page = "CLRSLean"

[order_children]
"CLRSLean" = [
  "CLRSLean.Chapter_02.Section_02_1_Insertion_Sort",
  "CLRSLean.Chapter_16.Section_16_3_Huffman_Codes",
  "CLRSLean.Chapter_23.Section_23_1_Growing_Minimum_Spanning_Trees",
  "CLRSLean.Chapter_23.Section_23_2_Kruskal_And_Prim",
]

[modules."CLRSLean.Chapter_02.Section_02_1_Insertion_Sort"]
title = "2.1. Insertion Sort / 插入排序"

[modules."CLRSLean.Chapter_16.Section_16_3_Huffman_Codes"]
title = "16.3. Huffman Codes / 哈夫曼编码"

[modules."CLRSLean.Chapter_23.Section_23_1_Growing_Minimum_Spanning_Trees"]
title = "23.1. Growing a Minimum Spanning Tree"

[modules."CLRSLean.Chapter_23.Section_23_2_Kruskal_And_Prim"]
title = "23.2. Kruskal and Prim"
```

## .lean 文件改写规范

参见 `CLAUDE.md`。核心要求：

1. 每个文件顶部必须有 `/-! ... -/` 模块文档块（页面标题 + 简介 + 主要结果）
2. 每个定义/定理前必须有 `/-- ... -/` 文档注释
3. 统一使用 `namespace CLRS`
4. 未完成证明用注释说明的 `sorry`

## CI/CD

### pages.yml (更新)

两个 job: `build` (构建 site) → `deploy` (部署到 Pages)

build 步骤: checkout → lean-action → lake build → doc-gen4 → lake build :literateHtml → 收集到 _site/ → upload artifact

deploy: 仅在 main 分支，deploy-pages

### lean_action_ci.yml (不变)

标准 lean-action CI，只验证编译。

## 实施步骤

1. 将 lakefile.toml 替换为 lakefile.lean
2. 创建 literate.toml
3. 重写 CLRSLean.lean（着陆页）
4. 给每个 .lean 文件加 /-! 模块文档块
5. 更新 pages.yml
6. 本地验证 lake build 通过
7. 本地验证 lake build :literateHtml 生成正确
8. 推送，观察 CI + Pages 部署
