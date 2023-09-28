local M = {}

vim.filetype.add({
  extension = {
      kb = "kibi"
  }
})


vim.cmd([[
    hi link @lsp.type.error.kibi            Error
    hi link @lsp.type.keyword.kibi          Keyword
    hi link @lsp.type.punctuation.kibi      Delimiter
    hi link @lsp.type.operator.kibi         Operator
    hi link @lsp.type.string.kibi           String
    hi link @lsp.type.number.kibi           Number
    hi link @lsp.type.type.kibi             Type
    hi link @lsp.type.type.parameter.kibi   Parameter
    hi link @lsp.type.type.variable.kibi    Variable
]])


--vim.lsp.set_log_level("debug")


local lspconfig = require "lspconfig"
local configs = require "lspconfig.configs"

configs.kibi_lsp = {
    default_config = {
        name = "kibi-lsp",
        filetypes = { "kibi" },

        cmd = { "target/debug/kibi-lsp" },
        --cmd = { "target/release/kibi-lsp" },

        root_dir = lspconfig.util.find_git_ancestor,
        single_file_support = true,

        on_new_config = function(new_config)
            new_config.flags = { debounce_text_changes = 10 }
        end,

        handlers = {
            ["workspace/semanticTokens/refresh"] = function(...)
                -- update info panel.
                local client = vim.lsp.get_active_clients({bufnr = info_panel_code_buffer})[1]
                if client then
                    --print("request info panel")
                    client.request("kibi/info_panel", {}, function(err, result)
                        if err then return end

                        --print("got info panel", vim.inspect(result))
                    end)
                end

                return vim.lsp.handlers["workspace/semanticTokens/refresh"](...)
            end,
        }
    },
}
lspconfig.kibi_lsp.setup({})



-- info panel.
local info_panel_window = nil
local info_panel_buffer = nil
local info_panel_code_buffer = nil

function M.open_info_panel()
    local BUFFER_OPTIONS = {
        swapfile = false,
        buftype = "nofile",
        modifiable = false,
        filetype = "kibi_info_panel",
        bufhidden = "wipe",
        buflisted = false,
    }

    -- @temp: reuse window.
    if info_panel_window then return end

    local old_window = vim.api.nvim_get_current_win()
    local old_buffer = vim.api.nvim_win_get_buf(old_window)

    local buffer = vim.api.nvim_create_buf(false, false)
    vim.api.nvim_buf_set_name(buffer, "kibi_info_view")
    for k, v in pairs(BUFFER_OPTIONS) do
        vim.bo[buffer][k] = v
    end

    vim.api.nvim_command("vsp")
    vim.api.nvim_command("wincmd L")

    local window = vim.api.nvim_get_current_win()
    vim.api.nvim_win_set_buf(window, buffer)

    vim.api.nvim_set_current_win(old_window)

    info_panel_window = window
    info_panel_buffer = buffer
    info_panel_code_buffer = old_buffer
end


return M

