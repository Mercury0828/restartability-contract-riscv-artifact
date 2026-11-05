# The Rocq development

51 files, Coq 8.15.0, standard library only (lists, relations, linear arithmetic).

```
bash verify.sh    # clean build in dependency order + Print Assumptions on 81 headline results
make              # the same files through _CoqProject
```

`VERIFY_LOG.txt` is the output of `verify.sh` for these sources. The list of files, in dependency
order, and the headline results checked by `Print Assumptions` are at the top of `verify.sh`. The
README at the root of the artifact maps the numbered results of the paper to their Rocq theorems.
