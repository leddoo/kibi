vim.lsp.set_log_level("debug")

if KIBI_CLIENT then
    print("stopping")
    vim.lsp.stop_client(KIBI_CLIENT)
end

vim.lsp.stop_client("kibi-lsp")

KIBI_CLIENT = vim.lsp.start({
  name = "kibi-lsp",

  cmd = {"target/debug/kibi-lsp"},

  root_dir = vim.fs.dirname(vim.fs.find({"hello.kb"}, { upward = true })[1]),
})

print(KIBI_CLIENT)

