# Problem manifests

Each benchmark problem has one `problems/<id>.toml` file. The file name must
match `id`, and every declaration listed in `holes` must carry
`@[eval_problem]` in the named Lean module.

```toml
id = "example_id"
title = "Human-readable title"
test = false
module = "HomotopyGroups.Example"
holes = ["example_theorem"]
submitter = "Contributor name"
source = "Stable bibliographic URL or citation"
notes = "Scope and formalization notes"
informal_solution = "Optional outline; omit for open conjectures"
```
