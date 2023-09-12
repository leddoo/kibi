local M = {}

vim.filetype.add({
  extension = {
      kb = "kibi"
  }
})


vim.lsp.set_log_level("debug")


local lspconfig = require 'lspconfig'
local configs = require 'lspconfig.configs'

configs.kibi_lsp = {
    default_config = {
        name = "kibi-lsp",
        filetypes = { "kibi" },
        cmd = { "target/debug/kibi-lsp" },
        single_file_support = true,
    },
}
lspconfig.kibi_lsp.setup({})


return M

