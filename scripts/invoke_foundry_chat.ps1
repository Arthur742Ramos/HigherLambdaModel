[CmdletBinding()]
param(
    [Parameter(Mandatory)]
    [string]$Prompt,

    [string]$SystemPrompt = "You are a helpful assistant.",

    [string]$FoundryDeploymentUrl,

    [string]$Endpoint = $env:AZURE_OPENAI_ENDPOINT,

    [string]$Deployment = $env:AZURE_OPENAI_DEPLOYMENT,

    [string]$ApiKey = $env:AZURE_OPENAI_API_KEY,

    [double]$Temperature,

    [switch]$RawJson
)

Set-StrictMode -Version Latest
$ErrorActionPreference = "Stop"

function Normalize-OpenAIEndpoint {
    param(
        [Parameter(Mandatory)]
        [string]$Value
    )

    $trimmed = $Value.Trim()
    if (-not ($trimmed -match "^https?://")) {
        $trimmed = "https://$trimmed"
    }

    $trimmed = $trimmed.TrimEnd("/")
    if ($trimmed -match "/openai/v1$") {
        return $trimmed
    }

    return "$trimmed/openai/v1"
}

function Resolve-FoundryDeploymentContext {
    param(
        [Parameter(Mandatory)]
        [string]$Value
    )

    $uri = [System.Uri]$Value
    $decodedPath = [System.Uri]::UnescapeDataString($uri.AbsolutePath)
    $match = [regex]::Match(
        $decodedPath,
        "accounts/(?<account>[^/]+)/deployments/(?<deployment>[^/]+)"
    )

    if (-not $match.Success) {
        throw "Could not extract the resource account and deployment from the Foundry deployment URL."
    }

    [pscustomobject]@{
        Endpoint = "https://$($match.Groups['account'].Value).openai.azure.com"
        Deployment = $match.Groups["deployment"].Value
    }
}

function Get-AzureOpenAIToken {
    $az = Get-Command az -ErrorAction SilentlyContinue
    if ($null -eq $az) {
        throw "Authentication failed: set AZURE_OPENAI_API_KEY or install Azure CLI and run 'az login'."
    }

    $token = (& az account get-access-token `
        --resource https://cognitiveservices.azure.com `
        --query accessToken `
        --output tsv).Trim()

    if (-not $token) {
        throw "Authentication failed: Azure CLI did not return an access token. Run 'az login' or set AZURE_OPENAI_API_KEY."
    }

    return $token
}

function Try-GetMemberValue {
    param(
        [Parameter(Mandatory)]
        $InputObject,

        [Parameter(Mandatory)]
        [string]$Name
    )

    if ($InputObject -is [System.Collections.IDictionary]) {
        if ($InputObject.Contains($Name)) {
            return $InputObject[$Name]
        }

        return $null
    }

    $property = $InputObject.PSObject.Properties[$Name]
    if ($null -eq $property) {
        return $null
    }

    return $property.Value
}

function Convert-ChatContentToText {
    param(
        [Parameter(Mandatory)]
        [AllowNull()]
        $Content
    )

    if ($null -eq $Content) {
        return ""
    }

    if ($Content -is [string]) {
        return $Content
    }

    if ($Content -is [System.Collections.IEnumerable]) {
        $parts = foreach ($item in $Content) {
            if ($item -is [string]) {
                $item
            } else {
                $text = Try-GetMemberValue -InputObject $item -Name "text"

                if ($null -ne $text) {
                    $text
                } else {
                    $item | ConvertTo-Json -Depth 10 -Compress
                }
            }
        }

        return ($parts -join "`n").Trim()
    }

    return ($Content | ConvertTo-Json -Depth 10 -Compress)
}

if ($FoundryDeploymentUrl) {
    $resolved = Resolve-FoundryDeploymentContext -Value $FoundryDeploymentUrl
    if (-not $PSBoundParameters.ContainsKey("Endpoint")) {
        $Endpoint = $resolved.Endpoint
    }
    if (-not $PSBoundParameters.ContainsKey("Deployment")) {
        $Deployment = $resolved.Deployment
    }
}

if (-not $ApiKey -and $env:AZURE_INFERENCE_CREDENTIAL) {
    $ApiKey = $env:AZURE_INFERENCE_CREDENTIAL
}

if (-not $Endpoint) {
    throw "No endpoint configured. Set AZURE_OPENAI_ENDPOINT or pass -Endpoint."
}

if (-not $Deployment) {
    throw "No deployment configured. Set AZURE_OPENAI_DEPLOYMENT, pass -Deployment, or pass -FoundryDeploymentUrl."
}

$headers = @{}
if ($ApiKey) {
    $headers["api-key"] = $ApiKey
} else {
    $headers["Authorization"] = "Bearer $(Get-AzureOpenAIToken)"
}

$messages = @()
if ($SystemPrompt) {
    $messages += @{
        role = "system"
        content = $SystemPrompt
    }
}
$messages += @{
    role = "user"
    content = $Prompt
}

$body = [ordered]@{
    model = $Deployment
    messages = $messages
}

if ($PSBoundParameters.ContainsKey("Temperature")) {
    $body.temperature = $Temperature
}

$uri = "$(Normalize-OpenAIEndpoint -Value $Endpoint)/chat/completions"
$response = Invoke-RestMethod `
    -Uri $uri `
    -Method Post `
    -Headers $headers `
    -Body ($body | ConvertTo-Json -Depth 10) `
    -ContentType "application/json"

if ($RawJson) {
    $response | ConvertTo-Json -Depth 20
    return
}

if ($null -eq $response.choices -or $response.choices.Count -eq 0) {
    throw "The model response did not contain any choices."
}

$text = Convert-ChatContentToText -Content $response.choices[0].message.content
if ($text) {
    Write-Output $text
} else {
    $response | ConvertTo-Json -Depth 20
}
