local M = {}

vim.filetype.add({
  extension = {
      kb = "kibi"
  }
})


vim.cmd([[
    hi link @lsp.type.keyword.kibi          Keyword
    hi link @lsp.type.punctuation.kibi      Delimiter
    hi link @lsp.type.operator.kibi         Operator
    hi link @lsp.type.string.kibi           String
    hi link @lsp.type.number.kibi           Number
    hi link @lsp.type.type.kibi             Type
    hi link @lsp.type.type.parameter.kibi   Parameter
    hi link @lsp.type.type.variable.kibi    Variable
]])


vim.lsp.set_log_level("debug")


local lspconfig = require 'lspconfig'
local configs = require 'lspconfig.configs'

configs.kibi_lsp = {
    default_config = {
        name = "kibi-lsp",
        filetypes = { "kibi" },

        cmd = { "target/debug/kibi-lsp" },
        --cmd = { "target/release/kibi-lsp" },

        single_file_support = true,

        on_new_config = function(new_config)
            new_config.flags = { debounce_text_changes = 10 }
        end,
    },
}
lspconfig.kibi_lsp.setup({})


return M

