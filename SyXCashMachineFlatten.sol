// SPDX-License-Identifier: MIT
// Inspired by https://solidity-by-example.org/defi/staking-rewards/
pragma solidity ^0.8.0;

// import "@openzeppelin/contracts/utils/ReentrancyGuard.sol";

// OpenZeppelin Contracts (last updated v5.0.0) (token/ERC20/IERC20.sol)

/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */
interface IERC20 {
    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);

    /**
     * @dev Returns the value of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the value of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves a `value` amount of tokens from the caller's account to `to`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address to, uint256 value) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets a `value` amount of tokens as the allowance of `spender` over the
     * caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 value) external returns (bool);

    /**
     * @dev Moves a `value` amount of tokens from `from` to `to` using the
     * allowance mechanism. `value` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(address from, address to, uint256 value) external returns (bool);
}

// OpenZeppelin Contracts (last updated v5.0.0) (access/Ownable.sol)

// OpenZeppelin Contracts (last updated v5.0.1) (utils/Context.sol)

/**
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }

    function _contextSuffixLength() internal view virtual returns (uint256) {
        return 0;
    }
}

/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * The initial owner is set to the address provided by the deployer. This can
 * later be changed with {transferOwnership}.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
abstract contract Ownable is Context {
    address private _owner;

    /**
     * @dev The caller account is not authorized to perform an operation.
     */
    error OwnableUnauthorizedAccount(address account);

    /**
     * @dev The owner is not a valid owner account. (eg. `address(0)`)
     */
    error OwnableInvalidOwner(address owner);

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the address provided by the deployer as the initial owner.
     */
    constructor(address initialOwner) {
        if (initialOwner == address(0)) {
            revert OwnableInvalidOwner(address(0));
        }
        _transferOwnership(initialOwner);
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        _checkOwner();
        _;
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view virtual returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if the sender is not the owner.
     */
    function _checkOwner() internal view virtual {
        if (owner() != _msgSender()) {
            revert OwnableUnauthorizedAccount(_msgSender());
        }
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby disabling any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        _transferOwnership(address(0));
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        if (newOwner == address(0)) {
            revert OwnableInvalidOwner(address(0));
        }
        _transferOwnership(newOwner);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Internal function without access restriction.
     */
    function _transferOwnership(address newOwner) internal virtual {
        address oldOwner = _owner;
        _owner = newOwner;
        emit OwnershipTransferred(oldOwner, newOwner);
    }
}

// OpenZeppelin Contracts (last updated v5.0.0) (utils/ReentrancyGuard.sol)

/**
 * @dev Contract module that helps prevent reentrant calls to a function.
 *
 * Inheriting from `ReentrancyGuard` will make the {nonReentrant} modifier
 * available, which can be applied to functions to make sure there are no nested
 * (reentrant) calls to them.
 *
 * Note that because there is a single `nonReentrant` guard, functions marked as
 * `nonReentrant` may not call one another. This can be worked around by making
 * those functions `private`, and then adding `external` `nonReentrant` entry
 * points to them.
 *
 * TIP: If you would like to learn more about reentrancy and alternative ways
 * to protect against it, check out our blog post
 * https://blog.openzeppelin.com/reentrancy-after-istanbul/[Reentrancy After Istanbul].
 */
abstract contract ReentrancyGuard {
    // Booleans are more expensive than uint256 or any type that takes up a full
    // word because each write operation emits an extra SLOAD to first read the
    // slot's contents, replace the bits taken up by the boolean, and then write
    // back. This is the compiler's defense against contract upgrades and
    // pointer aliasing, and it cannot be disabled.

    // The values being non-zero value makes deployment a bit more expensive,
    // but in exchange the refund on every call to nonReentrant will be lower in
    // amount. Since refunds are capped to a percentage of the total
    // transaction's gas, it is best to keep them low in cases like this one, to
    // increase the likelihood of the full refund coming into effect.
    uint256 private constant NOT_ENTERED = 1;
    uint256 private constant ENTERED = 2;

    uint256 private _status;

    /**
     * @dev Unauthorized reentrant call.
     */
    error ReentrancyGuardReentrantCall();

    constructor() {
        _status = NOT_ENTERED;
    }

    /**
     * @dev Prevents a contract from calling itself, directly or indirectly.
     * Calling a `nonReentrant` function from another `nonReentrant`
     * function is not supported. It is possible to prevent this from happening
     * by making the `nonReentrant` function external, and making it call a
     * `private` function that does the actual work.
     */
    modifier nonReentrant() {
        _nonReentrantBefore();
        _;
        _nonReentrantAfter();
    }

    function _nonReentrantBefore() private {
        // On the first call to nonReentrant, _status will be NOT_ENTERED
        if (_status == ENTERED) {
            revert ReentrancyGuardReentrantCall();
        }

        // Any calls to nonReentrant after this point will fail
        _status = ENTERED;
    }

    function _nonReentrantAfter() private {
        // By storing the original value once again, a refund is triggered (see
        // https://eips.ethereum.org/EIPS/eip-2200)
        _status = NOT_ENTERED;
    }

    /**
     * @dev Returns true if the reentrancy guard is currently set to "entered", which indicates there is a
     * `nonReentrant` function in the call stack.
     */
    function _reentrancyGuardEntered() internal view returns (bool) {
        return _status == ENTERED;
    }
}

// OpenZeppelin Contracts (last updated v5.0.0) (token/ERC20/utils/SafeERC20.sol)

// OpenZeppelin Contracts (last updated v5.0.0) (token/ERC20/extensions/IERC20Permit.sol)

/**
 * @dev Interface of the ERC20 Permit extension allowing approvals to be made via signatures, as defined in
 * https://eips.ethereum.org/EIPS/eip-2612[EIP-2612].
 *
 * Adds the {permit} method, which can be used to change an account's ERC20 allowance (see {IERC20-allowance}) by
 * presenting a message signed by the account. By not relying on {IERC20-approve}, the token holder account doesn't
 * need to send a transaction, and thus is not required to hold Ether at all.
 *
 * ==== Security Considerations
 *
 * There are two important considerations concerning the use of `permit`. The first is that a valid permit signature
 * expresses an allowance, and it should not be assumed to convey additional meaning. In particular, it should not be
 * considered as an intention to spend the allowance in any specific way. The second is that because permits have
 * built-in replay protection and can be submitted by anyone, they can be frontrun. A protocol that uses permits should
 * take this into consideration and allow a `permit` call to fail. Combining these two aspects, a pattern that may be
 * generally recommended is:
 *
 * ```solidity
 * function doThingWithPermit(..., uint256 value, uint256 deadline, uint8 v, bytes32 r, bytes32 s) public {
 *     try token.permit(msg.sender, address(this), value, deadline, v, r, s) {} catch {}
 *     doThing(..., value);
 * }
 *
 * function doThing(..., uint256 value) public {
 *     token.safeTransferFrom(msg.sender, address(this), value);
 *     ...
 * }
 * ```
 *
 * Observe that: 1) `msg.sender` is used as the owner, leaving no ambiguity as to the signer intent, and 2) the use of
 * `try/catch` allows the permit to fail and makes the code tolerant to frontrunning. (See also
 * {SafeERC20-safeTransferFrom}).
 *
 * Additionally, note that smart contract wallets (such as Argent or Safe) are not able to produce permit signatures, so
 * contracts should have entry points that don't rely on permit.
 */
interface IERC20Permit {
    /**
     * @dev Sets `value` as the allowance of `spender` over ``owner``'s tokens,
     * given ``owner``'s signed approval.
     *
     * IMPORTANT: The same issues {IERC20-approve} has related to transaction
     * ordering also apply here.
     *
     * Emits an {Approval} event.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     * - `deadline` must be a timestamp in the future.
     * - `v`, `r` and `s` must be a valid `secp256k1` signature from `owner`
     * over the EIP712-formatted function arguments.
     * - the signature must use ``owner``'s current nonce (see {nonces}).
     *
     * For more information on the signature format, see the
     * https://eips.ethereum.org/EIPS/eip-2612#specification[relevant EIP
     * section].
     *
     * CAUTION: See Security Considerations above.
     */
    function permit(address owner, address spender, uint256 value, uint256 deadline, uint8 v, bytes32 r, bytes32 s)
        external;

    /**
     * @dev Returns the current nonce for `owner`. This value must be
     * included whenever a signature is generated for {permit}.
     *
     * Every successful call to {permit} increases ``owner``'s nonce by one. This
     * prevents a signature from being used multiple times.
     */
    function nonces(address owner) external view returns (uint256);

    /**
     * @dev Returns the domain separator used in the encoding of the signature for {permit}, as defined by {EIP712}.
     */
    // solhint-disable-next-line func-name-mixedcase
    function DOMAIN_SEPARATOR() external view returns (bytes32);
}

// OpenZeppelin Contracts (last updated v5.0.0) (utils/Address.sol)

/**
 * @dev Collection of functions related to the address type
 */
library Address {
    /**
     * @dev The ETH balance of the account is not enough to perform the operation.
     */
    error AddressInsufficientBalance(address account);

    /**
     * @dev There's no code at `target` (it is not a contract).
     */
    error AddressEmptyCode(address target);

    /**
     * @dev A call to an address target failed. The target may have reverted.
     */
    error FailedInnerCall();

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://consensys.net/diligence/blog/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.8.20/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        if (address(this).balance < amount) {
            revert AddressInsufficientBalance(address(this));
        }

        (bool success,) = recipient.call{value: amount}("");
        if (!success) {
            revert FailedInnerCall();
        }
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain `call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason or custom error, it is bubbled
     * up by this function (like regular Solidity function calls). However, if
     * the call reverted with no returned reason, this function reverts with a
     * {FailedInnerCall} error.
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     */
    function functionCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     */
    function functionCallWithValue(address target, bytes memory data, uint256 value) internal returns (bytes memory) {
        if (address(this).balance < value) {
            revert AddressInsufficientBalance(address(this));
        }
        (bool success, bytes memory returndata) = target.call{value: value}(data);
        return verifyCallResultFromTarget(target, success, returndata);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a static call.
     */
    function functionStaticCall(address target, bytes memory data) internal view returns (bytes memory) {
        (bool success, bytes memory returndata) = target.staticcall(data);
        return verifyCallResultFromTarget(target, success, returndata);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a delegate call.
     */
    function functionDelegateCall(address target, bytes memory data) internal returns (bytes memory) {
        (bool success, bytes memory returndata) = target.delegatecall(data);
        return verifyCallResultFromTarget(target, success, returndata);
    }

    /**
     * @dev Tool to verify that a low level call to smart-contract was successful, and reverts if the target
     * was not a contract or bubbling up the revert reason (falling back to {FailedInnerCall}) in case of an
     * unsuccessful call.
     */
    function verifyCallResultFromTarget(address target, bool success, bytes memory returndata)
        internal
        view
        returns (bytes memory)
    {
        if (!success) {
            _revert(returndata);
        } else {
            // only check if target is a contract if the call was successful and the return data is empty
            // otherwise we already know that it was a contract
            if (returndata.length == 0 && target.code.length == 0) {
                revert AddressEmptyCode(target);
            }
            return returndata;
        }
    }

    /**
     * @dev Tool to verify that a low level call was successful, and reverts if it wasn't, either by bubbling the
     * revert reason or with a default {FailedInnerCall} error.
     */
    function verifyCallResult(bool success, bytes memory returndata) internal pure returns (bytes memory) {
        if (!success) {
            _revert(returndata);
        } else {
            return returndata;
        }
    }

    /**
     * @dev Reverts with returndata if present. Otherwise reverts with {FailedInnerCall}.
     */
    function _revert(bytes memory returndata) private pure {
        // Look for revert reason and bubble it up if present
        if (returndata.length > 0) {
            // The easiest way to bubble the revert reason is using memory via assembly
            /// @solidity memory-safe-assembly
            assembly {
                let returndata_size := mload(returndata)
                revert(add(32, returndata), returndata_size)
            }
        } else {
            revert FailedInnerCall();
        }
    }
}

/**
 * @title SafeERC20
 * @dev Wrappers around ERC20 operations that throw on failure (when the token
 * contract returns false). Tokens that return no value (and instead revert or
 * throw on failure) are also supported, non-reverting calls are assumed to be
 * successful.
 * To use this library you can add a `using SafeERC20 for IERC20;` statement to your contract,
 * which allows you to call the safe operations as `token.safeTransfer(...)`, etc.
 */
library SafeERC20 {
    using Address for address;

    /**
     * @dev An operation with an ERC20 token failed.
     */
    error SafeERC20FailedOperation(address token);

    /**
     * @dev Indicates a failed `decreaseAllowance` request.
     */
    error SafeERC20FailedDecreaseAllowance(address spender, uint256 currentAllowance, uint256 requestedDecrease);

    /**
     * @dev Transfer `value` amount of `token` from the calling contract to `to`. If `token` returns no value,
     * non-reverting calls are assumed to be successful.
     */
    function safeTransfer(IERC20 token, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeCall(token.transfer, (to, value)));
    }

    /**
     * @dev Transfer `value` amount of `token` from `from` to `to`, spending the approval given by `from` to the
     * calling contract. If `token` returns no value, non-reverting calls are assumed to be successful.
     */
    function safeTransferFrom(IERC20 token, address from, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeCall(token.transferFrom, (from, to, value)));
    }

    /**
     * @dev Increase the calling contract's allowance toward `spender` by `value`. If `token` returns no value,
     * non-reverting calls are assumed to be successful.
     */
    function safeIncreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        uint256 oldAllowance = token.allowance(address(this), spender);
        forceApprove(token, spender, oldAllowance + value);
    }

    /**
     * @dev Decrease the calling contract's allowance toward `spender` by `requestedDecrease`. If `token` returns no
     * value, non-reverting calls are assumed to be successful.
     */
    function safeDecreaseAllowance(IERC20 token, address spender, uint256 requestedDecrease) internal {
        unchecked {
            uint256 currentAllowance = token.allowance(address(this), spender);
            if (currentAllowance < requestedDecrease) {
                revert SafeERC20FailedDecreaseAllowance(spender, currentAllowance, requestedDecrease);
            }
            forceApprove(token, spender, currentAllowance - requestedDecrease);
        }
    }

    /**
     * @dev Set the calling contract's allowance toward `spender` to `value`. If `token` returns no value,
     * non-reverting calls are assumed to be successful. Meant to be used with tokens that require the approval
     * to be set to zero before setting it to a non-zero value, such as USDT.
     */
    function forceApprove(IERC20 token, address spender, uint256 value) internal {
        bytes memory approvalCall = abi.encodeCall(token.approve, (spender, value));

        if (!_callOptionalReturnBool(token, approvalCall)) {
            _callOptionalReturn(token, abi.encodeCall(token.approve, (spender, 0)));
            _callOptionalReturn(token, approvalCall);
        }
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     */
    function _callOptionalReturn(IERC20 token, bytes memory data) private {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves. We use {Address-functionCall} to perform this call, which verifies that
        // the target address contains contract code and also asserts for success in the low-level call.

        bytes memory returndata = address(token).functionCall(data);
        if (returndata.length != 0 && !abi.decode(returndata, (bool))) {
            revert SafeERC20FailedOperation(address(token));
        }
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     *
     * This is a variant of {_callOptionalReturn} that silents catches all reverts and returns a bool instead.
     */
    function _callOptionalReturnBool(IERC20 token, bytes memory data) private returns (bool) {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves. We cannot use {Address-functionCall} here since this should return false
        // and not revert is the subcall reverts.

        (bool success, bytes memory returndata) = address(token).call(data);
        return success && (returndata.length == 0 || abi.decode(returndata, (bool))) && address(token).code.length > 0;
    }
}

interface IUniswapV2Router01 {
    function factory() external pure returns (address);

    function WETH() external pure returns (address);

    function quote(uint256 amountA, uint256 reserveA, uint256 reserveB) external pure returns (uint256 amountB);

    function getAmountsIn(uint256 amountOut, address[] calldata path)
        external
        view
        returns (uint256[] memory amounts);
  
}

// pragma solidity >=0.6.2;

interface IUniswapV2Router02 is IUniswapV2Router01 {
    function swapExactTokensForTokensSupportingFeeOnTransferTokens(
        uint256 amountIn,
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external;
}

error NeedsMoreThanZero();

interface ITreasury {
    function withdraw(uint256 tokenAmount) external;
}

struct Fee {
    uint256 buy;
    uint256 sell;
}

struct Fees {
    Fee transactionTax;
    uint256 buyBackTax;
    uint256 holderTax;
    uint256 lpTax;
}


contract AddressRegistry {
    constructor(address treasury) {
        coreTreasuryAddress = treasury;
    }

    address public constant coreAddress = address(0x6e8cE91124D57C37556672F8889cb89aF52a6746); //Cbank Token
    address public coreTreasuryAddress; //CBank  Treasury
    address public constant collateralAddress = address(0x55d398326f99059fF775485246999027B3197955); //BUSD
    address public constant routerAddress = address(0x10ED43C718714eb63d5aA57B78B54704E256024E);
}

contract CairoCashMachine is ReentrancyGuard {
    using SafeERC20 for IERC20;

    AddressRegistry public immutable registry;
    address immutable defaultReferrer;
    IERC20 public immutable collateralToken;
    IERC20 immutable coreToken;
    ITreasury immutable coreTreasury;
    IUniswapV2Router02 public immutable collateralRouter;
    uint256 public s_lastUpdateTime;
    uint256 public s_totalSupply;
    uint256 public s_rewardPerTokenStored;
    uint256 public minOut;
    uint256[] depositRefShare = [1000, 200, 100, 50, 50, 50, 50];
    uint256[] withdrawRefShare = [500, 100, 100, 100, 100, 50, 50];
    uint256[] public REFERRENCE_APR = [1.095 ether, 1.46 ether, 1.825 ether];

    struct referral_data {
        uint256 available;
        uint256 referred;
        address[] myReferrs;
    }

    mapping(address => uint256) public s_rewards_claimed;
    mapping(address => uint256) public s_userRewardPerTokenPaid;
    mapping(address => uint256) public s_rewards;
    mapping(address => uint256) public s_max_payout;
    mapping(address => address) public referral;
    mapping(address => referral_data) public referralData;
    mapping(address => uint256) public s_balances;
    mapping(string => address) public s_custom_code;
    mapping(address => string) public s_address_to_code;

    event Referred(address referrer, address user, uint256 time);
    event Staked(address indexed user, uint256 indexed amount);
    event RewardsClaimed(address indexed user, uint256 indexed amount);

    constructor(address default_referrer, string memory default_code, address _coreTreasury,uint256 minimum_payout_claimable) {
        // Setup default refercode
        defaultReferrer = default_referrer;
        s_custom_code[default_code] = default_referrer;
        s_address_to_code[defaultReferrer] = default_code;
        //init reg
        registry = new AddressRegistry(_coreTreasury);
        coreToken = IERC20(registry.coreAddress());
        collateralToken = IERC20(registry.collateralAddress());

        //the collateral router cannot  be upgraded in the future
        collateralRouter = IUniswapV2Router02(registry.routerAddress());

        //treasury setup
        coreTreasury = ITreasury(registry.coreTreasuryAddress());
        //One-time approve
        collateralToken.forceApprove(address(collateralRouter), type(uint256).max);
        coreToken.forceApprove(address(collateralRouter), type(uint256).max);
        minOut =minimum_payout_claimable;
    }

    /**
     * @notice How much reward a token gets based on how long it's been in and during which "snapshots"
     */
    function rewardPerToken() public view returns (uint256) {
        if (s_totalSupply == 0) {
            return s_rewardPerTokenStored;
        }
        return s_rewardPerTokenStored + ((block.timestamp - s_lastUpdateTime) * rewardRate());
    }

    function rewardRate() public view returns (uint256) {
        uint256 referenceApr = choosePayout();

  
        uint256 _rewardRate = (referenceApr  / (365  * 24 hours));
        return _rewardRate;
    }

    function choosePayout() public view returns (uint256) {
        uint256 balance = collateralToken.balanceOf(address(this));
        uint256 index = balance > 500000 ether ? 2 : balance > 100000 ether ? 1 : 0;
        return REFERRENCE_APR[index]; // Divide by 10000 for decimal precision
    }
    /**
     * @notice How much reward a user has _earned
     */

    function _earned(address account) private view returns (uint256) {
        return
           ( ((s_balances[account] * (rewardPerToken() - s_userRewardPerTokenPaid[account])) / 1e18) ) + s_rewards[account];
    }

    function totalEarnings(address account) public view returns (uint256) {
        uint256 claimed = s_rewards_claimed[account] + _earned(account) + referralData[account].available;
        return claimed;
    }

    function earned(address account) public view returns (uint256 earnings) {
        if (s_rewards_claimed[account] == s_max_payout[account]) return 0;
        if (totalEarnings(account) > s_max_payout[account]) {
            earnings = s_max_payout[account] - s_rewards_claimed[account];
        } else {
            earnings = _earned(account) + referralData[account].available;
        }
        return earnings;
    }
    /**
     * @notice Deposit tokens into this contract
     * @param amount | How much to stake
     */

    function stake(uint256 amount, string calldata referCode)
        external
        updateReward(msg.sender)
        nonReentrant
        moreThanZero(amount)
    {
        require(
            s_balances[msg.sender] == 0 || s_max_payout[msg.sender] == s_rewards_claimed[msg.sender],
            "Only one deposit is available at a time"
        );
        address referralAddress = s_custom_code[referCode];
        require(referralAddress != msg.sender, "Can't use your own code.");
        s_totalSupply += amount;
        s_balances[msg.sender] = amount;
        s_max_payout[msg.sender] = (amount * 16_500) / 10_000;
        s_rewards_claimed[msg.sender] = 0;

        emit Staked(msg.sender, amount);
        uint256 refPaid = referralDeposit(referralAddress, amount);
        uint256 coreAmount = ((amount - refPaid) * 5500 ) / 10_000;
        collateralToken.safeTransferFrom(msg.sender, address(this), amount);
        accumulateCore(address(coreTreasury), coreAmount);
    }

    function referralDeposit(address referrer, uint256 _amount) internal returns (uint256) {
        // Set referrer to defaultReferrer if it's invalid
        if (referrer == address(0) || referral[referrer] == address(0)) referrer = defaultReferrer;
        address currentReferrer = referrer;

        // Set referrer for the sender if not already set
        if (referral[msg.sender] == address(0)) {
            referral[msg.sender] = currentReferrer;
            referralData[currentReferrer].referred++;
            referralData[currentReferrer].myReferrs.push(msg.sender);
        }
        currentReferrer = referral[msg.sender]; // set referrer for the sender

        return distributionLoop(currentReferrer, _amount, true);
    }

    function distributionLoop(address currentReferrer, uint256 _amount, bool deposit)
        private
        returns (uint256 rewardPaid)
    {
        uint256[] memory shares;
        if (deposit) {
            shares = depositRefShare;
        } else {
            shares = withdrawRefShare;
        }
        for (uint256 i = 0; i < 7 && currentReferrer != address(0); i++) {
            uint256 rewAmount = (shares[i] * _amount ) / 10_000;
            uint256 max = s_max_payout[currentReferrer];
            uint256 rewards_earned = totalEarnings(currentReferrer);
            bool isDefault = currentReferrer == defaultReferrer;

            // Check if the referrer has reached the maximum payout
            if (rewards_earned >= max && !isDefault) {
                currentReferrer = referral[currentReferrer];
                continue;
            }
            // Adjust rewAmount if it exceeds the maximum payout
            if ((rewards_earned + rewAmount) > max && !isDefault) {
                rewAmount = max - rewards_earned;
            }
            // Update available rewards and rewardPaid
            referralData[currentReferrer].available += rewAmount;
            rewardPaid += rewAmount;
            emit Referred(currentReferrer, msg.sender, block.timestamp);
            // Move to the next referrer
            currentReferrer = referral[currentReferrer];
        }
        return rewardPaid;
    }

    function referralWithdraw(uint256 _amount) private returns (uint256) {
        address currentReferrer = referral[msg.sender];
        return distributionLoop(currentReferrer, _amount, false);
    }

    function claimReward() external updateReward(msg.sender) nonReentrant {
        uint256 claimed = s_rewards_claimed[msg.sender];
        require(s_balances[msg.sender] > 0, "You need to deposit funds before claiming rewards.");
        require(claimed < s_max_payout[msg.sender], "Max Payout Reached!!!");
        uint256 reward = s_rewards[msg.sender];
        if (reward + claimed > s_max_payout[msg.sender]) {
            reward = s_max_payout[msg.sender] - claimed;
        }
        require(reward>=minOut || (s_max_payout[msg.sender] - claimed) < minOut,"Invalid rewards amount");
        if (reward > collateralToken.balanceOf(address(this))) {
            // Calcuating amount to lquidate
            // using 112 % of reward amount to convert as 10% will be paid as tax, 10 % of 112 = 12 remaining 108
            uint256 amountToGet = (reward * 112) / 100;
            (, uint256 _coreAmount) = estimateCollateralToCore(amountToGet);
            require(coreToken.balanceOf(address(coreTreasury)) >= _coreAmount,"Wait for treasury to be paid");
            liquidateCore(address(this), _coreAmount);
        }
        s_rewards[msg.sender] -= 0;
        referralData[msg.sender].available = 0;
        s_rewards_claimed[msg.sender] += reward;
        emit RewardsClaimed(msg.sender, reward);
        reward = calculateAdditionalTax(msg.sender, reward);
        reward -= referralWithdraw(reward);
        collateralToken.safeTransfer(msg.sender, reward);
    }

    function updateReferralCode(string calldata code) external {
        require(
            s_custom_code[code] == address(0) || s_custom_code[code] == msg.sender,
            "Already used! Please select a different code!"
        );
        require(s_balances[msg.sender] > 0, "You need to deposit funds before referring others.");
        s_custom_code[code] = msg.sender;
        s_address_to_code[msg.sender] = code;
    }

    /**
     *
     */
    /* Modifiers Functions */
    /**
     *
     */
    modifier updateReward(address account) {
        s_rewardPerTokenStored = rewardPerToken();
        s_lastUpdateTime = block.timestamp;
        if (account != address(0)) {
            s_rewards[account] = earned(account);
            s_userRewardPerTokenPaid[account] = s_rewardPerTokenStored;
        }
        _;
    }

    modifier moreThanZero(uint256 amount) {
        if (amount < 200e18) {
            revert NeedsMoreThanZero();
        }
        _;
    }

    function liquidateCore(address destination, uint256 _amount) private returns (uint256 collateralAmount) {
        //Convert from collateral to backed
        address[] memory path = new address[](3);

        path[0] = address(coreToken);
        path[1] = collateralRouter.WETH();
        path[2] = address(collateralToken);

        //withdraw from treasury
        coreTreasury.withdraw(_amount);
        // Fethes lp tax and calculate estimaed amount out.
        
      
        uint256 initialBalance = collateralToken.balanceOf(destination);

        collateralRouter.swapExactTokensForTokensSupportingFeeOnTransferTokens(
            _amount, 0, path, destination, block.timestamp
        );

        collateralAmount = collateralToken.balanceOf(destination) - (initialBalance);
    }

    function accumulateCore(address destination, uint256 _amount) private {
        //Convert from collateral to backed
        address[] memory path = new address[](3);

        path[0] = address(collateralToken);
        path[1] = collateralRouter.WETH();
        path[2] = address(coreToken);
        collateralRouter.swapExactTokensForTokensSupportingFeeOnTransferTokens(
            _amount,0, path, destination, block.timestamp
        );
    }

    function estimateCollateralToCore(uint256 collateralAmount)
        public
        view
        returns (uint256 wethAmount, uint256 coreAmount)
    {
        //Convert from collateral to core using router
        address[] memory path = new address[](3);
        path[0] = address(coreToken);
        path[1] = collateralRouter.WETH();
        path[2] = address(collateralToken);

        uint256[] memory amounts = collateralRouter.getAmountsIn(collateralAmount, path);

        //Use core router to get amount of coreTokens required to cover
        wethAmount = amounts[1];
        coreAmount = amounts[0];
    }

    function calculateAdditionalTax(address user, uint256 amount) internal view returns (uint256) {
        uint256 balance = s_balances[user];
        uint256 depositShare = (balance * 100) / collateralToken.balanceOf(address(this));
        uint256 taxableAmount = (amount * taxFrequency(depositShare)) / 10_000;
        uint256 netWithdrawal = amount - taxableAmount;
        return netWithdrawal;
    }

    function taxFrequency(uint256 depositShare) internal pure returns (uint256) {
        if (depositShare >= 1) {
            if (depositShare == 1) return 5;
            else if (depositShare == 2) return 750; // 7.5%

            else if (depositShare == 3) return 1000; // 10%

            else if (depositShare == 4) return 1250; // 12.5%

            else if (depositShare == 5) return 1500; // 15%

            else if (depositShare == 6) return 1750; // 17.5%

            else if (depositShare == 7) return 2000; // 20%

            else if (depositShare == 8) return 2500; // 25%

            else if (depositShare == 9) return 3000; // 30%

            else if (depositShare >= 10) return 3500; // 35%
        }
        return 0;
    }

    function myList(address user) public view returns (address[] memory) {
        return referralData[user].myReferrs;
    }

    function getStakes(address account) public view returns (uint256) {
        return s_balances[account];
    }


   

}
