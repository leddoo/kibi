if KIBI_CLIENT then
    print("stopping")
    vim.lsp.stop_client(KIBI_CLIENT)
end

vim.filetype.add({
  extension = {
      kb = "kibi"
  }
})

KIBI_CLIENT = vim.lsp.start({
  name = "kibi-lsp",

  cmd = {"target/debug/kibi-lsp"},
})

print(KIBI_CLIENT)

